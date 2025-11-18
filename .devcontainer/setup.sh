#!/bin/bash
set -e

echo "🔧 Setting up Symcrust development environment..."

# Install system dependencies
echo "📦 Installing system dependencies..."
sudo apt-get update
sudo apt-get install -y build-essential cmake curl git pkg-config libssl-dev

# Install Rust with specific components
echo "🦀 Setting up Rust toolchain..."
rustup component add rustc-dev llvm-tools-preview rust-analyzer clippy rustfmt

# Install elan (Lean version manager) and Lean
echo "📐 Installing Lean 4..."
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"
echo 'export PATH="$HOME/.elan/bin:$PATH"' >> ~/.bashrc

# Navigate to proofs directory and let Lake install the correct Lean version
cd proofs
elan override set $(cat lean-toolchain | tr -d '\n')
lake exe cache get || true
lake build || echo "⚠️  Lake build may fail until Aeneas is set up"

# Setup Aeneas (assuming it's in a sibling directory as per lakefile.lean)
echo "🔍 Setting up Aeneas..."
cd ../..
if [ ! -d "aeneas" ]; then
  echo "📥 Cloning Aeneas repository..."
  git clone https://github.com/AeneasVerif/aeneas.git
  cd aeneas
  
  # Install OCaml and dependencies for Aeneas
  echo "📦 Installing OCaml and OPAM..."
  sudo apt-get install -y opam m4 pkg-config libgmp-dev
  opam init -y --disable-sandboxing --compiler=5.2.0
  eval $(opam env)
  
  # Install OCaml dependencies for Aeneas
  echo "📦 Installing OCaml dependencies..."
  opam install -y ppx_deriving visitors easy_logging zarith yojson core_unix \
    odoc ocamlgraph menhir ocamlformat unionFind progress domainslib dune
  
  # Setup Charon (required by Aeneas) - this will clone and build Charon
  echo "📥 Setting up Charon..."
  make setup-charon
  
  # Build Aeneas
  echo "🔨 Building Aeneas..."
  make build
else
  echo "✅ Aeneas directory already exists"
  cd aeneas
  # Ensure Charon is set up even if Aeneas exists
  if [ ! -d "charon" ]; then
    echo "📥 Setting up Charon..."
    make setup-charon
  fi
  eval $(opam env) 2>/dev/null || true
fi

cd ../symcrust

# Build the Rust project
echo "🔨 Building Rust project..."
cargo build

# Build Lean proofs
echo "📊 Building Lean proofs..."
cd proofs
lake build

echo "✅ Setup complete! You're ready to develop."
echo ""
echo "Quick commands:"
echo "  - cargo build          # Build Rust code"
echo "  - cargo test           # Run Rust tests"
echo "  - cd proofs && lake build  # Build Lean proofs"
