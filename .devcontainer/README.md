# Codespaces Configuration

This directory contains the configuration for GitHub Codespaces.

## What's Included

- **Rust**: Latest stable Rust with `rustc-dev`, `llvm-tools-preview`, and `rust-analyzer`
- **Lean 4**: Version 4.24.0 (as specified in `lean-toolchain`)
- **Aeneas**: Automatically cloned and built
- **VS Code Extensions**:
  - Rust Analyzer
  - Lean 4
  - Even Better TOML
  - CodeLLDB (for debugging)

## First Time Setup

When you create a new Codespace, the setup script will automatically:

1. Install system dependencies (CMake, build tools, etc.)
2. Configure Rust with the required components
3. Install Lean 4 via elan
4. Clone and build Aeneas (if not present)
5. Build the Rust project
6. Build the Lean proofs

This may take 5-10 minutes on first launch.

## Manual Setup

If you need to re-run setup:

```bash
bash .devcontainer/setup.sh
```

## Working with the Project

### Rust Development
```bash
cargo build
cargo test
cargo clippy
```

### Lean Development
```bash
cd proofs
lake build
lake exe spec_tests
```

## Notes

- Cargo cache is persisted in `.cargo-cache` to speed up rebuilds
- Aeneas is expected to be in `../../aeneas` relative to the project root
- The Lean toolchain version is automatically detected from `proofs/lean-toolchain`
