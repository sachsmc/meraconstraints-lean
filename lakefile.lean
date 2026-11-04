import Lake
open Lake DSL

package «MeraConstraints» where
  leanOptions := #[⟨`autoImplicit, false⟩]

-- The API generator is only loaded for documentation builds.
meta if get_config? env = some "dev" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "v4.31.0"

-- Verso renders the existing literate Lean chapters without a second proof source.
require verso from git "https://github.com/leanprover/verso" @ "v4.31.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0"

@[default_target]
lean_lib MeraConstraints
