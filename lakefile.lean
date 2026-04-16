import Lake
open Lake DSL System

package «lean-sail»

@[default_target]
lean_lib Sail where
  leanOptions := #[⟨`weak.linter.style.nameCheck, false⟩]
  moreLinkObjs := #[⟨.packageTarget .anonymous `bitvec_opt_c⟩]

target bitvec_opt_c pkg : FilePath := do
  let srcPath := pkg.dir / "Sail" / "bitvec_opt.c"
  let oFile := pkg.irDir / "bitvec_opt.o"
  let src ← inputTextFile srcPath
  buildO oFile src (compiler := "cc")
    (traceArgs := #["-I", (← getLeanIncludeDir).toString])
