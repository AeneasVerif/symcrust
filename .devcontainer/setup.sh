#!/bin/bash
set -e  # Exit on error
set -x  # Print commands as they execute

echo "🔧 Setting up Symcrust development environment..."
echo "Current directory: $(pwd)"
echo "User: $(whoami)"

# Install system dependencies
echo "📦 Installing system dependencies..."
sudo apt-get update
sudo apt-get install -y build-essential cmake curl git pkg-config libssl-dev

# Install Rust with specific components
echo "🦀 Setting up Rust toolchain..."
rustup component add rustc-dev llvm-tools-preview rust-analyzer clippy rustfmt

# Install elan (Lean version manager) and Lean
echo "📐 Installing Lean 4..."
echo "Downloading elan installer..."
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"
echo 'export PATH="$HOME/.elan/bin:$PATH"' >> ~/.bashrc
echo "Elan installed successfully"
elan --version || echo "Warning: elan not found in PATH"

# Navigate to proofs directory and let Lake install the correct Lean version
echo "Setting up Lean project..."
cd proofs
echo "Current directory: $(pwd)"
echo "Lean toolchain file contents:"
cat lean-toolchain
elan override set $(cat lean-toolchain | tr -d '\n')
echo "Lean version:"
lean --version
lake exe cache get || echo "Warning: cache get failed, continuing..."
lake build || echo "⚠️  Lake build may fail until Aeneas is set up"
cd ..

# Setup Aeneas (assuming it's in a sibling directory as per lakefile.lean)
echo "🔍 Setting up Aeneas..."
cd ../..
echo "Current directory: $(pwd)"
echo "Contents:"
ls -la

if [ ! -d "aeneas" ]; then
  echo "📥 Cloning Aeneas repository..."
  git clone https://github.com/AeneasVerif/aeneas.git
  cd aeneas
  echo "Aeneas cloned to: $(pwd)"
  
  # Install OCaml and dependencies for Aeneas
  echo "📦 Installing OCaml and OPAM..."
  sudo apt-get install -y opam m4 pkg-config libgmp-dev
  
  echo "Initializing OPAM with OCaml 5.2.0..."
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
  
  echo "✅ Aeneas setup complete"
  ls -la bin/
else
  echo "✅ Aeneas directory already exists at: $(pwd)/aeneas"
  cd aeneas
  # Ensure Charon is set up even if Aeneas exists
  if [ ! -d "charon" ]; then
    echo "📥 Setting up Charon..."
    make setup-charon
  fi
  eval $(opam env) 2>/dev/null || true
fi

echo "Returning to symcrust directory..."
cd ../symcrust
echo "Current directory: $(pwd)"

# Build the Rust project
echo "🔨 Building Rust project..."
echo "Current directory: $(pwd)"
cargo build
echo "✅ Rust build complete"

# Build Lean proofs
echo "📊 Building Lean proofs..."
cd proofs
lake build
echo "✅ Lean proofs build complete"
cd ..

echo ""
echo "✅ Setup complete! You're ready to develop."
echo ""
echo "Quick commands:"
echo "  - cargo build          # Build Rust code"
echo "  - cargo test           # Run Rust tests"
echo "  - cd proofs && lake build  # Build Lean proofs"
echo ""
echo "Environment summary:"
echo "  - Rust: $(rustc --version)"
echo "  - Lean: $(lean --version)"
if [ -f ../../aeneas/bin/aeneas ]; then
  echo "  - Aeneas: ✅ Available at ../../aeneas/bin/aeneas"
else
  echo "  - Aeneas: ⚠️  Not found"
fi
