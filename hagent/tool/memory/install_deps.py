#!/usr/bin/env python3
"""
Install required dependencies for the embedding retrieval system.
"""

import subprocess
import sys
import os

def install_dependencies():
    """Install the required dependencies."""
    try:
        # Check if sentence-transformers is installed
        try:
            import sentence_transformers
            print("✓ sentence-transformers is already installed.")
        except ImportError:
            print("Installing sentence-transformers...")
            subprocess.check_call([sys.executable, "-m", "pip", "install", "sentence-transformers"])
            print("✓ sentence-transformers installed successfully.")
        
        # Check if scikit-learn is installed
        try:
            import sklearn
            print("✓ scikit-learn is already installed.")
        except ImportError:
            print("Installing scikit-learn...")
            subprocess.check_call([sys.executable, "-m", "pip", "install", "scikit-learn"])
            print("✓ scikit-learn installed successfully.")
        
        # Check if numpy is installed
        try:
            import numpy
            print("✓ numpy is already installed.")
        except ImportError:
            print("Installing numpy...")
            subprocess.check_call([sys.executable, "-m", "pip", "install", "numpy"])
            print("✓ numpy installed successfully.")
        
        # Check if ruamel.yaml is installed
        try:
            import ruamel.yaml
            print("✓ ruamel.yaml is already installed.")
        except ImportError:
            print("Installing ruamel.yaml...")
            subprocess.check_call([sys.executable, "-m", "pip", "install", "ruamel.yaml"])
            print("✓ ruamel.yaml installed successfully.")
            
        print("\nAll dependencies installed successfully! You can now run the embedding retrieval system.")
        print("\nTo test the system, run:")
        print("  python test_embedding_retrieval.py --generate --verbose")
        
    except Exception as e:
        print(f"Error installing dependencies: {e}")
        return False
    
    return True

if __name__ == "__main__":
    print("Installing dependencies for embedding retrieval system...\n")
    success = install_dependencies()
    
    if success:
        sys.exit(0)
    else:
        sys.exit(1)