import os
import re
import sys
from datetime import datetime
import google.generativeai as genai
from github import Github, Auth

# --- Constants ---
MAX_DIFF_TOKENS = 1_500_000
COMMENT_IDENTIFIER = "<!-- gemini-pr-summary -->"
SORRY_KEYWORDS = ["theorem", "def", "lemma", "instance", "example", "corollary", "proposition"]

# --- AI Summary Generation ---
def generate_ai_summary(diff):
    """Generates a concise, high-level summary of a git diff using the Gemini API."""
    if len(diff) > MAX_DIFF_TOKENS:
        diff = diff[:MAX_DIFF_TOKENS]
        truncated = True
    else:
        truncated = False

    model = genai.GenerativeModel('gemini-2.5-pro')
    prompt = f"""
    Please provide a concise, high-level summary of the following git diff.
    Focus on the key changes and their purpose. Do not describe the changes line-by-line.
    Use bullet points for clarity if needed.

    Diff:
    {diff}
    """
    try:
        response = model.generate_content(prompt)
        return response.text, truncated
    except Exception as e:
        return f"Error generating summary: {e}", False

# --- Diff Analysis ---
def analyze_diff(diff):
    """Parses a git diff to extract statistics and track 'sorry's using stable identifiers."""
    files_changed = set()
    lines_added = 0
    lines_removed = 0
    added_sorries = []
    removed_sorries = []
    affected_sorries = []

    current_file = ""
    old_line_num = 0
    new_line_num = 0
    current_decl_header = ""
    current_decl_name = ""

    file_path_regex = re.compile(r'diff --git a/(.+) b/(.+)')
    hunk_header_regex = re.compile(r'@@ -(\d+),?(\d*) \+(\d+),?(\d*) @@')
    name_extract_regex = re.compile(
        r".*?(?:theorem|lemma|def|instance|example|opaque|abbrev|inductive|structure)\s+"
        r"([^\s\(\{:]+)"
    )

    raw_added = {}
    raw_removed = {}

    for line in diff.splitlines():
        file_match = file_path_regex.match(line)
        if file_match:
            current_file = file_match.group(2)
            files_changed.add(current_file)
            current_decl_header = ""
            current_decl_name = ""
            continue

        hunk_match = hunk_header_regex.match(line)
        if hunk_match:
            old_line_num = int(hunk_match.group(1))
            new_line_num = int(hunk_match.group(3))
            current_decl_header = ""
            current_decl_name = ""
            continue

        if line.startswith("---") or line.startswith("+++"):
            continue


        # --- Only process .lean files for sorry tracking ---
        if not current_file.endswith(".lean"):
            continue
            
        elif line.startswith('+'):
            lines_added += 1
            
        elif line.startswith('-'):
            lines_removed += 1

        if current_file.endswith(".lean"):
            stripped_line = line.lstrip('+- ')
            if any(stripped_line.startswith(keyword + ' ') for keyword in SORRY_KEYWORDS):
                current_decl_header = re.sub(r"^[+-]\s*", "", line)
                name_match = name_extract_regex.match(current_decl_header)
                if name_match:
                    current_decl_name = name_match.group(1)

            if 'sorry' in line and current_decl_name:
                comment_pos = line.find("--")
                sorry_pos = line.find("sorry")
                if comment_pos != -1 and sorry_pos > comment_pos:
                    continue

                stable_id = f"{current_decl_name}@{current_file}"
                sorry_info = {
                    'id': stable_id,
                    'file': current_file,
                    'name': current_decl_name,
                    'header': current_decl_header.split(":=")[0].strip()
                }

                if line.startswith('+'):
                    sorry_info['line'] = new_line_num
                    raw_added[stable_id] = sorry_info
                elif line.startswith('-'):
                    sorry_info['line'] = old_line_num
                    raw_removed[stable_id] = sorry_info

            if line.startswith('+'):
                new_line_num += 1
            elif line.startswith('-'):
                old_line_num += 1
            else:
                old_line_num += 1
                new_line_num += 1

    added_ids = set(raw_added.keys())
    removed_ids = set(raw_removed.keys())

    affected_ids = added_ids.intersection(removed_ids)
    
    for sid in affected_ids:
        affected_sorries.append({
            'id': sid,
            'file': raw_added[sid]['file'],
            'context': raw_added[sid]['header'],
            'old_line': raw_removed[sid]['line'],
            'new_line': raw_added[sid]['line']
        })

    for sid in added_ids - affected_ids:
        added_sorries.append(f"`{raw_added[sid]['header']}` in `{raw_added[sid]['file']}`")

    for sid in removed_ids - affected_ids:
        removed_sorries.append(f"`{raw_removed[sid]['header']}` in `{raw_removed[sid]['file']}`")

    stats = {
        "files_changed": len(files_changed),
        "lines_added": lines_added,
        "lines_removed": lines_removed,
    }
    return stats, added_sorries, removed_sorries, affected_sorries

# --- Comment Formatting ---
def format_summary(ai_summary, stats, added_sorries, removed_sorries, affected_sorries, truncated, issues):
    """Formats the final summary comment in Markdown."""
    
    summary = f"### 🤖 Gemini PR Summary\n\n{COMMENT_IDENTIFIER}\n\n"
    summary += f"{ai_summary}\n"
    if truncated:
        summary += "> *Note: The diff was too large to be fully analyzed and was truncated.*\\n"
    
    summary += "\n---\n\n"
    summary += "**Analysis of Changes**\n\n"
    summary += "| Metric | Count |\n| --- | --- |\n"
    summary += f"| 📝 **Files Changed** | {stats['files_changed']} |\n"
    summary += f"| ✅ **Lines Added** | {stats['lines_added']} |\n"
    summary += f"| ❌ **Lines Removed** | {stats['lines_removed']} |\n"

    summary += "\n---\n\n"
    summary += "**`sorry` Tracking**\n\n"
    
    if removed_sorries:
        summary += f"*   ✅ **Removed:** {len(removed_sorries)} `sorry`(s)\n"
        for sorry in removed_sorries:
            summary += f"    *   {sorry}\n"
    
    if added_sorries:
        summary += f"*   ❌ **Added:** {len(added_sorries)} `sorry`(s)\n"
        for sorry in added_sorries:
            summary += f"    *   {sorry}\n"

    if affected_sorries:
        summary += f"*   ✏️ **Affected:** {len(affected_sorries)} `sorry`(s) (line number changed)\n"
        for sorry in affected_sorries:
            # Find the corresponding issue by searching for the stable ID in the issue body
            issue_link = ""
            stable_id_comment = f"<!-- sorry-tracker-id: {sorry['id']} -->"
            print(f"Searching for ID: '{stable_id_comment}'") # DEBUG
            for issue in issues:
                print(f"Checking issue #{issue.number} body: '{issue.body}'") # DEBUG
                if issue.body and stable_id_comment in issue.body:
                    issue_link = f" (Issue #{issue.number})"
                    break
            summary += f"    *   `{sorry['context']}` in `{sorry['file']}` moved from L{sorry['old_line']} to L{sorry['new_line']}{issue_link}\n"


    if not added_sorries and not removed_sorries and not affected_sorries:
        summary += "*   No `sorry`s were added, removed, or affected.\n"

    timestamp = datetime.utcnow().strftime("%Y-%m-%d %H:%M UTC")
    summary += f"\n---\n\n*Last updated: {timestamp}. See the [main CI run](https://github.com/{os.environ['GITHUB_REPOSITORY']}/actions) for build status.*"
    
    return summary


def find_sorry_issues(repo):
    """Finds all open issues with the 'proof wanted' label."""
    try:
        return repo.get_issues(state="open", labels=["proof wanted"])
    except Exception as e:
        print(f"Warning: Could not fetch issues. {e}")
        return []

# --- GitHub Interaction ---
def post_github_comment(summary):
    """Finds and updates an existing comment or creates a new one."""
    token = os.environ["GITHUB_TOKEN"]
    repo_name = os.environ["GITHUB_REPOSITORY"]
    pr_number = int(os.environ["PR_NUMBER"])

    auth = Auth.Token(token)
    g = Github(auth=auth)
    repo = g.get_repo(repo_name)
    pr = repo.get_pull(pr_number)

    existing_comment = None
    for comment in pr.get_issue_comments():
        if COMMENT_IDENTIFIER in comment.body:
            existing_comment = comment
            break
    
    if existing_comment:
        existing_comment.edit(summary)
        print("Updated existing comment.")
    else:
        pr.create_issue_comment(summary)
        print("Created a new comment.")

# --- Main Execution ---
if __name__ == "__main__":
    if "GEMINI_API_KEY" not in os.environ:
        print("Error: GEMINI_API_KEY environment variable not set.")
        sys.exit(1)
    genai.configure(api_key=os.environ["GEMINI_API_KEY"])

    try:
        with open("pr.diff", "r") as f:
            diff = f.read()
    except FileNotFoundError:
        print("Error: pr.diff not found.")
        sys.exit(1)

    stats, added_sorries, removed_sorries, affected_sorries = analyze_diff(diff)
    ai_summary, truncated = generate_ai_summary(diff)
    
    # Fetch sorry issues
    token = os.environ.get("GITHUB_TOKEN")
    repo_name = os.environ.get("GITHUB_REPOSITORY")
    issues = []
    if token and repo_name:
        auth = Auth.Token(token)
        g = Github(auth=auth)
        repo = g.get_repo(repo_name)
        issues = find_sorry_issues(repo)
        print(f"Found {issues.totalCount} issues with 'proof wanted' label.") # DEBUG

    final_summary = format_summary(ai_summary, stats, added_sorries, removed_sorries, affected_sorries, truncated, issues)
    
    if "GITHUB_TOKEN" not in os.environ:
        print("Not in GitHub Actions context. Printing summary instead of posting:")
        print(final_summary)
    else:
        post_github_comment(final_summary)
