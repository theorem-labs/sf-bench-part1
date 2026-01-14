# SF-Bench Part 1: Rocq to Lean Translation Verification

This repository contains verified translations of all of the statements all of the the **Logical Foundations** volume of [Software Foundations](https://softwarefoundations.cis.upenn.edu/) from Rocq to Lean 4.

The repository includes 869 translation results, each with a formally verified proof that the Lean translation is semantically equivalent to the original Rocq definition. Note that these statements cover all of LF through either the statement itself, or one of the dependencies.

## Repository Structure

```
sf-bench-part1/
├── theories/                    # Core Rocq verification infrastructure
│   ├── Original.v               # Original Software Foundations definitions
│   ├── Imported.v               # Imports Lean definitions into Rocq
│   ├── Checker.v                # Combined checker file
│   └── Isomorphisms.v           # Combined isomorphism proofs
├── results/                     # 869 individual translation results
│   └── result-N/
│       ├── solution.lean        # Lean translation of a theorem/definition
│       ├── lean.out             # lean4export output
│       ├── scores.json          # Evaluation scores for the translation
│       └── theories/
│           ├── Checker/         # Compile this to verify the translation
│           ├── Interface/       # Module interface definitions
│           └── Isomorphisms/    # Type isomorphism proofs
├── Dockerfile                   # Docker environment for verification
└── problem-deps.json            # Dependencies between problems
```

## How Verification Works

Each translation is verified through a type isomorphism proof that demonstrates the Lean translation is semantically equivalent to the original Rocq definition:

1. **Lean Translation**: `solution.lean` contains the Lean 4 translation of a Rocq theorem or definition

2. **Export**: `lean4export` exports the Lean definitions to `lean.out`, a text format that can be imported into Rocq

3. **Import into Rocq**: The `LeanImport` library imports the Lean definitions into Rocq (see `theories/Imported.v`)

4. **Isomorphism Proof**: The files in `theories/Isomorphisms/` prove that the original Rocq definition is type-isomorphic to the imported Lean definition

5. **Verification**: If the Checker file compiles successfully, the translation is verified correct

## Verifying the Results

You can verify the results using the provided Docker environment.

### Prerequisites

- Docker installed on your machine
- Sufficient disk space (~5GB for the image)

### Step 1: Build the Docker Image

```bash
docker build -t sf-bench-part1 .
```

This builds an image with:
- Rocq/Coq 9.1.0 (custom fork with recursive-assumptions support)
- rocq-lean-import (for importing Lean definitions into Rocq)
- Lean 4.20.0-rc5 (via elan)
- lean4export tool

### Step 2: Run a Container

```bash
docker run -it --rm -v $(pwd):/workdir sf-bench-part1
```

### Step 3: Verify a Result

To verify a single result (e.g., result-1):

#### 3a. Verify Lean Compilation

```bash
cd /workdir/results/result-1
lean solution.lean
```

A successful compilation (no errors) means the Lean code is valid.

#### 3b. Verify lean4export Output

```bash
cd /workdir/results/result-1
lean4export solution.lean > lean.out.new
diff lean.out lean.out.new
```

No diff output means the export matches.

#### 3c. Verify Rocq Checker Compiles

Copy the result's theories into the main theories directory and compile:

```bash
eval $(opam env)
cd /workdir

# Copy the result's lean.out as Imported.out
cp results/result-1/lean.out theories/Imported.out

# Copy the result's Interface, Isomorphisms, and Checker folders
cp -r results/result-1/theories/* theories/

# Compile the Checker (this verifies the translation is correct)
cd theories
rocq c -Q . IsomorphismChecker Checker/*.v
```

If the Checker compiles without errors, the translation is verified correct.

## Quick Verification Checklist

1. Build the Docker image successfully
2. Verify `lean solution.lean` compiles for a sample result
3. Verify `lean4export` output matches the stored `lean.out`
4. Verify the Rocq Checker compiles for the result

## Understanding the Results

### solution.lean

Each `solution.lean` file contains a Lean 4 translation. For example:

```lean
/-
  Lean translation of consequentia_mirabilis from LF.Logic

  Original Rocq definition:
    Definition consequentia_mirabilis := forall P:Prop, (~P -> P) -> P.
-/
def Original_LF__DOT__Logic_LF_Logic_consequentia__mirabilis : Prop :=
  forall (P : Prop), (not P -> P) -> P
```

### scores.json

Contains evaluation scores for the isomorphism proofs:

```json
{
  "U_original__U2_lf_dot_U_logic__U2_lf__U_logic__consequentia____mirabilis__iso": 1.0
}
```

A score of 1.0 indicates a complete, verified isomorphism.

### Isomorphism Files

The `.v` files in `theories/Isomorphisms/` contain Rocq proofs that establish a bijection between the original and translated definitions, proving semantic equivalence.

## Tool Versions

The Docker image uses these specific versions:

| Tool | Version | Notes |
|------|---------|-------|
| Rocq/Coq | 9.1.0 | From [JasonGross/coq#v9.1+recursive-assumptions](https://github.com/JasonGross/coq.git) |
| Lean | 4.20.0-rc5 | Installed via elan |
| lean4export | c9f8373 | [leanprover/lean4export](https://github.com/leanprover/lean4export) |
| rocq-lean-import | latest | [rocq-community/rocq-lean-import](https://github.com/rocq-community/rocq-lean-import) |

## License

See [LICENSE](LICENSE) for details.
