import Lake

open System Lake DSL

package CompPoly where
  version := v!"0.1.0"
  testDriver := "CompPolyTests"

require "leanprover-community" / mathlib @ git "v4.32.0"

/-- Directory holding the C sources of the trusted native boundary. -/
def nativeDir : FilePath := __dir__ / "native"

/-- Output directory for compiled native objects and static archives. -/
def nativeBuildDir : FilePath := __dir__ / ".lake" / "build" / "native"

/-- Compile `native/<src>` into the static archive `.lake/build/native/lib<name>.a`. -/
def nativeLib (name src : String) (extraCcArgs : Array String := #[]) :
    FetchM (Job FilePath) := do
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

extern_lib libcomppoly_mont256 _pkg := nativeLib "comppoly_mont256" "comppoly_mont256.c"

/-- Linker arguments for binaries that call the extern symbols of `lib<name>.a`. -/
def nativeLinkArgs (name : String) : Array String :=
  #["-L", nativeBuildDir.toString, s!"-l{name}"]

@[default_target]
lean_lib CompPoly where
  moreLinkArgs := nativeLinkArgs "comppoly_mont256"

lean_lib CompPolyTests where
  srcDir := "tests"
  moreLinkArgs := nativeLinkArgs "comppoly_mont256"

lean_lib CompPolyBenchLib where
  srcDir := "bench"
  globs := #[Glob.submodules `CompPolyBench]

lean_exe CompPolyBench where
  srcDir := "bench"
  moreLinkArgs := nativeLinkArgs "comppoly_mont256"

lean_exe CompPolyMont256ExtTests where
  srcDir := "tests"
  root := `CompPolyTests.Fields.Montgomery.Native256Ext
  moreLinkArgs := nativeLinkArgs "comppoly_mont256"
