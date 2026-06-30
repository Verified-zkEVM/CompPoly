import Lake

open System Lake DSL

package CompPoly where
  version := v!"0.1.0"
  testDriver := "CompPolyTests"

require "leanprover-community" / mathlib @ git "v4.30.0"

def nativeDir : FilePath := __dir__ / "native"

def nativeBuildDir : FilePath := __dir__ / ".lake" / "build" / "native"

def nativeLib (name src : String) (extraCcArgs : Array String := #[]) : FetchM (Job FilePath) := do
  let srcFile := nativeDir / src
  let oFile := nativeBuildDir / s!"{name}.o"
  let libFile := nativeBuildDir / s!"lib{name}.a"
  let srcJob ← inputTextFile srcFile
  buildFileAfterDep libFile srcJob fun _srcTrace => do
    compileO oFile srcFile (#["-O3", "-I", (← getLeanIncludeDir).toString] ++ extraCcArgs)
    createParentDirs libFile
    removeFileIfExists libFile
    proc {
      cmd := (← getLeanAr).toString
      args := #["rcs", libFile.toString, oFile.toString]
    }

extern_lib liblean_goldilocks_native _pkg := nativeLib "goldilocks_native" "goldilocks_native.c"

def nativeLinkArgs (name : String) : Array String :=
  #["-L", nativeBuildDir.toString, s!"-l{name}"]

@[default_target]
lean_lib CompPoly where
  moreLinkArgs := nativeLinkArgs "goldilocks_native"

lean_lib CompPolyTests where
  srcDir := "tests"
  moreLinkArgs := nativeLinkArgs "goldilocks_native"

lean_lib CompPolyBenchLib where
  srcDir := "bench"
  globs := #[Glob.submodules `CompPolyBench]

lean_exe CompPolyBench where
  srcDir := "bench"

lean_exe CompPolyGoldilocksFastExtTests where
  srcDir := "tests"
  root := `CompPolyTests.Fields.Goldilocks.FastExt
  moreLinkArgs := nativeLinkArgs "goldilocks_native"
