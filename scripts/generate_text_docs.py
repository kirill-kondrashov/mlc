import os
from pathlib import Path
import re

SOURCE_DIR = Path("../Mlc")
DOCS_DIR = Path("../docs")
DOCS_DIR.mkdir(exist_ok=True)

FILES = [
    "MainConjecture", "Yoccoz", "InfinitelyRenormalizable", "LcAtOfShrink",
    "Quadratic/Complex/Groetzsch", "Quadratic/Complex/Basic", "Quadratic/Complex/Green",
    "Quadratic/Complex/GreenLemmas", "Quadratic/Complex/Puzzle", "Quadratic/Complex/PuzzleLemmas",
    "Quadratic/Complex/PuzzleLemmas2", "Quadratic/Complex/Escape"
]

def generate_stub(lean_file):
    base_name = Path(lean_file).stem
    tex_path = DOCS_DIR / f"{base_name}.tex"
    
    with open(SOURCE_DIR / f"{lean_file}.lean", "r") as f:
        content = f.read()
    
    # Simple docstring extraction: find module docstring /-! ... -/
    module_doc = ""
    match = re.search(r"/-\!(.*?)-/", content, re.DOTALL)
    if match:
        module_doc = match.group(1).strip()
    
    # Create tex content
    tex_content = f"\\section{{{base_name}}}\n"
    tex_content += f"\\textit{{Source: \\texttt{{{lean_file}.lean}}}}\n\n"
    
    if module_doc:
        tex_content += "\\begin{quotation}\n"
        tex_content += module_doc.replace("\n", " ") + "\n"
        tex_content += "\\end{quotation}\n\n"
    else:
        tex_content += "This module contains the formal definitions and proofs.\n"

    # Simple regex to find theorems and their docstrings
    # Matches: /-* doc -/ theorem/lemma name ... :=
    pattern = re.compile(r'/\*\*(.*?)\*/\s*(?:theorem|lemma|def)\s+(\w+)', re.DOTALL)
    # Lean 4 docstrings use /-- ... -/
    pattern_lean4 = re.compile(r'/--(.*?)-/\s*(?:theorem|lemma|def)\s+(\w+)', re.DOTALL)
    
    # Let's try to capture them.
    # We will just append them as subsections
    
    for match in pattern_lean4.finditer(content):
        doc = match.group(1).strip()
        name = match.group(2)
        tex_content += f"\\subsection*{{{name.replace('_', '\\_')}}}\n"
        tex_content += f"{doc}\n\n"

        
    with open(tex_path, "w") as f:
        f.write(tex_content)
    print(f"Generated {tex_path}")

if __name__ == "__main__":
    for f in FILES:
        generate_stub(f)
