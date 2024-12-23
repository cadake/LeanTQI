import Lake
open Lake DSL

package «LeanTQI» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,      -- Pretty-print `fun a ↦ b`
    ⟨`autoImplicit, false⟩,       -- Disable auto-implicit arguments
    ⟨`relaxedAutoImplicit, false⟩ -- Disable relaxed auto-implicit arguments
  ]
  -- add any additional package configuration options here
  -- moreLinkArgs := #[
  --   "-L./.lake/packages/LeanCopilot/.lake/build/lib",
  --   "-lctranslate2"
  -- ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require checkdecls from git
  "https://github.com/PatrickMassot/checkdecls.git"

require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

-- require LeanCopilot from git
--   "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.6.0"

@[default_target]
lean_lib «LeanTQI» where
  -- add any library configuration options here
