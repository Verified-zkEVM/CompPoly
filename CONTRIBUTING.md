## Contributing to CompPoly

We enthusiastically welcome contributions to CompPoly!

Whether you are fixing bugs, improving documentation, or adding new formalizations, your input is valuable. We particularly encourage contributions that address:

<!-- TODO * **Active formalizations:** Please see the list of active formalization efforts and their blueprints -->
* **Open Issues:** Please see the list of open issues for bugs, requested features, and specific formalization tasks. Issues tagged as `good first issue` or `help wanted` are great places to start.
* **Roadmap Goals:** We are working on a [ROADMAP](https://github.com/Verified-zkEVM/CompPoly/blob/dhsorens/roadmap/ROADMAP.md) outlining the planned direction and major goals for the library.
* **Documentation:** Documentation is actively being worked and will be available as soon as possible.

If you are interested in contributing but unsure where to begin, please get in touch.

<!-- TODO some information on a Lean blueprint -->

### Style Guide

CompPoly aims to align closely with the established conventions of the Lean community, particularly those used in `mathlib` and `cslib`. Please follow the mathlib Style Guide:

* The [style guide](https://leanprover-community.github.io/contribute/style.html)
* A guide on the [naming convention](https://leanprover-community.github.io/contribute/naming.html)
* The [documentation style](https://leanprover-community.github.io/contribute/doc.html)

Adhering to this style guide ensures consistency across the library, making it easier for everyone to read, understand, and maintain the code. Our [linting script](scripts/lint-style.sh) helps enforce some aspects of the style guide and runs in the CI. **Please ensure your code passes the linter checks.**

#### Citation Standards

When referencing papers in Lean docstrings:

* **Use citation keys in text**: Reference papers with citation keys like `[ACFY24]` rather than full titles or URLs.

* **Include a References section**: Each file that cites papers should have a `## References` section in its docstring header:
  ```lean
  ## References
  
  * [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
      with Super-Fast Verification*][ACFY24]
  * [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S., *Proximity Gaps
      for Reed-Solomon Codes*][BCIKS20]
  ```
  Format: `* [Author Last Name, First Initial, *Title*][citation_key]`.

* **Add BibTeX entries**: All academic papers must have entries in `blueprint/src/references.bib`. When adding a new paper, add the BibTeX entry, use the citation key in your Lean file, and list it in the References section.

* **Non-academic references**: Implementation references (GitHub repos, specifications) may include URLs directly and typically don't need BibTeX entries.

## Code of Conduct

To ensure a welcoming and collaborative environment, CompPoly follows the principles outlined in the [mathlib Code of Conduct](https://github.com/leanprover-community/mathlib4/blob/master/CODE_OF_CONDUCT.md). By participating in this project (e.g., contributing code, opening issues, commenting in discussions), you agree to abide by its terms. Please treat fellow contributors with respect. Unacceptable behavior can be reported to the project maintainers.

## Licensing

Like many other Lean projects, CompPoly is licensed under the terms of the Apache License 2.0 license. The full license text can be found in the [LICENSE](LICENSE) file. By contributing to ArkLib, you agree that your contributions will be licensed under this same license. Ensure you are comfortable with these terms before submitting contributions.
