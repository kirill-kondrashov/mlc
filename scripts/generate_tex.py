import os
import re

def parse_lean_file(filepath):
    with open(filepath, 'r') as f:
        content = f.read()

    # Extract module name/namespace if needed, but we mostly care about theorems/defs
    # We want to extract blocks of:
    # /-- docstring -/
    # (theorem|lemma|def|axiom) name ...
    
    # Regex to find docstrings and associated declarations
    # This is a heuristic parser
    pattern = re.compile(r'(/--\s*(.*?)\s*-/)\s*((?:theorem|lemma|def|axiom|structure|opaque)\s+(\w+).*?)(?=\n\n|\n/--|$)', re.DOTALL)
    
    matches = pattern.findall(content)
    
    items = []
    for doc_block, doc_content, decl_line, name in matches:
        # Clean up docstring
        # Remove "Proof idea:" prefix if we want to format it specifically, or just keep it
        # We will format it for LaTeX
        
        # Check if it has "Proof idea" or similar
        proof_desc = ""
        details_desc = ""
        description = doc_content.strip()
        
        # Split description and proof idea if explicitly marked
        if "Proof idea:" in description:
            parts = description.split("Proof idea:")
            description = parts[0].strip()
            proof_desc = parts[1].strip()
        elif "Proof:" in description:
            parts = description.split("Proof:")
            description = parts[0].strip()
            proof_desc = parts[1].strip()
        elif "Details:" in description:
            parts = description.split("Details:")
            description = parts[0].strip()
            details_desc = parts[1].strip()
        
        items.append({
            'name': name,
            'type': decl_line.split()[0], # theorem, lemma, etc
            'decl': decl_line.strip(),
            'description': description,
            'proof_desc': proof_desc,
            'details_desc': details_desc,
            'full_doc': doc_content
        })
    return items

def escape_latex(text):
    # Escape special characters in text for LaTeX
    
    # Mappings for TEXT mode
    special_chars_text = {
        '\\': r'\textbackslash{}',
        '&': r'\&',
        '%': r'\%',
        '$': r'\$', # Escaped in text mode
        '#': r'\#',
        '_': r'\_',
        '{': r'\{',
        '}': r'\}',
        '~': r'\textasciitilde{}',
        '^': r'\^{}',
    }
    ordered_chars_text = ['\\', '&', '%', '$', '#', '_', '{', '}', '~', '^']
    
    # Mappings for MATH mode (inside $...$)
    # We generally preserve formatting but might want to map unicode
    special_chars_math = {
        '%': r'\%', # Still comment char
        '#': r'\#',
        # Do not escape _ ^ \ { } & (alignment) etc
    }
    
    # Unicode replacements
    # Text mode: wrap in math delimiters
    unicode_replacements_text = {
        'π': r'$\pi$',
        '∈': r'$\in$',
        '⊆': r'$\subseteq$',
        '∪': r'$\cup$',
        '∩': r'$\cap$',
        '→': r'$\to$',
        '↔': r'$\leftrightarrow$',
        '∀': r'$\forall$',
        '∃': r'$\exists$',
        '≤': r'$\le$',
        '≥': r'$\ge$',
        '≠': r'$\ne$',
        'ℂ': r'$\mathbb{C}$',
        'ℝ': r'$\mathbb{R}$',
        'ℕ': r'$\mathbb{N}$',
        'ℤ': r'$\mathbb{Z}$',
        '𝓝': r'$\mathcal{N}$',
    }
    
    # Math mode: straight replacement
    unicode_replacements_math = {
        'π': r'\pi',
        '∈': r'\in',
        '⊆': r'\subseteq',
        '∪': r'\cup',
        '∩': r'\cap',
        '→': r'\to',
        '↔': r'\leftrightarrow',
        '∀': r'\forall',
        '∃': r'\exists',
        '≤': r'\le',
        '≥': r'\ge',
        '≠': r'\ne',
        'ℂ': r'\mathbb{C}',
        'ℝ': r'\mathbb{R}',
        'ℕ': r'\mathbb{N}',
        'ℤ': r'\mathbb{Z}',
        '𝓝': r'\mathcal{N}',
    }

    # Split by backticks first (CODE blocks)
    parts = text.split('`')
    result = ""
    for i, part in enumerate(parts):
        if i % 2 == 1:
            # CODE BLOCK (inside backticks)
            # Escape everything for texttt
            escaped = part
            for char in ordered_chars_text:
                replacement = special_chars_text[char]
                escaped = escaped.replace(char, replacement)
            
            # Use text unicode replacements but without the $ wrapper? 
            # Or just let them be and hope listings/font handles it?
            # The current setup seems to rely on literate replacements in listings.
            # But here we are in \texttt{}.
            # Let's map unicode to latex math inside $...$ inside texttt? 
            # \texttt{... $\pi$ ...} works.
            for u, l in unicode_replacements_text.items():
                escaped = escaped.replace(u, l)
                
            result += f"\\texttt{{{escaped}}}"
        else:
            # TEXT/MATH segments
            # Split by '$' to find math mode
            math_parts = part.split('$')
            for j, subpart in enumerate(math_parts):
                if j % 2 == 1:
                    # MATH MODE
                    escaped = subpart
                    # Minimal escaping
                    escaped = escaped.replace('%', r'\%')
                    escaped = escaped.replace('#', r'\#')
                    
                    for u, l in unicode_replacements_math.items():
                        escaped = escaped.replace(u, l)
                        
                    result += f"${escaped}$"
                else:
                    # TEXT MODE
                    escaped = subpart
                    for char in ordered_chars_text:
                        replacement = special_chars_text[char]
                        escaped = escaped.replace(char, replacement)
                        
                    for u, l in unicode_replacements_text.items():
                        escaped = escaped.replace(u, l)
                        
                    result += escaped
            
    return result

def generate_tex(filename, items, module_name):
    # Escape underscores in filename for title
    # AND escape the title itself!
    title = escape_latex(module_name)
    tex_content = f"\\section{{{title}}}\n\n"
    
    for item in items:
        name = item['name'].replace('_', r'\_')
        
        # Format the description (convert markdown links to latex, etc?)
        # For now, minimal formatting
        desc = escape_latex(item['description'])
        proof = escape_latex(item['proof_desc'])
        details = escape_latex(item['details_desc'])
        
        tex_content += f"\\subsection*{{{item['type'].capitalize()} {name}}}\n"
        
        if desc:
            tex_content += f"\\textbf{{Description:}} {desc}\n\n"
            
        if proof:
            tex_content += f"\\textbf{{Proof Description:}} {proof}\n\n"

        if details:
            tex_content += f"\\textbf{{Details:}} {details}\n\n"
            
        # We also want to show the formal statement (decl)
        # We'll use verbatim or lstlisting
        # Extract the signature (first line or until := or by)
        decl = item['decl']
        # Truncate at := or by to avoid dumping the whole proof if regex captured too much
        # My regex captures until next docstring, which is too much.
        # Let's clean up decl.
        # Actually, the regex group 3 matches `((?:theorem|lemma|def|axiom|structure)\s+(\w+).*?)`
        # But `.*?` is non-greedy, stops at lookahead `(?=\n\n|\n/--|$)`.
        # So it captures the whole body until empty line or next doc.
        # We probably only want the statement.
        
        # Naive truncation at ':=\n' or 'by\n' or similar might be safer
        # For now let's just show the first few lines of declaration
        decl_lines = decl.split('\n')
        statement = []
        for line in decl_lines:
            statement.append(line)
            if ":=" in line or "by" in line:
                break
        statement_str = "\n".join(statement)
        
        tex_content += "\\begin{lstlisting}[language=Lean]\n"
        tex_content += statement_str + "\n"
        tex_content += "\\end{lstlisting}\n\n"
        
    return tex_content

def main():
    source_dir = '../Mlc'
    docs_dir = '../docs'
    
    # Map of file path to module name
    files = [
        ('MainConjecture.lean', 'Main Conjecture'),
        ('LcAtOfShrink.lean', 'Local Connectivity from Shrinking'),
        ('Yoccoz.lean', 'Yoccoz Theorem'),
        ('InfinitelyRenormalizable.lean', 'Infinitely Renormalizable Case'),
        ('Quadratic/Complex/PuzzleLemmas2.lean', 'Puzzle Lemmas (Correspondence & Openness)'),
        ('Quadratic/Complex/Escape.lean', 'Escape Lemma'),
        ('Quadratic/Complex/Green.lean', 'Green\'s Function'),
        ('Quadratic/Complex/Puzzle.lean', 'Puzzle Definitions'),
        ('Quadratic/Complex/PuzzleLemmas.lean', 'Basic Puzzle Lemmas'),
        ('Quadratic/Complex/Basic.lean', 'Basic Definitions'),
        ('Quadratic/Complex/GreenLemmas.lean', 'Green\'s Function Lemmas'),
    ]
    
    for rel_path, title in files:
        full_path = os.path.join(source_dir, rel_path)
        if not os.path.exists(full_path):
            print(f"Skipping {full_path} (not found)")
            continue
            
        items = parse_lean_file(full_path)
        
        # Output filename
        base_name = os.path.basename(rel_path).replace('.lean', '.tex')
        out_path = os.path.join(docs_dir, base_name)
        
        with open(out_path, 'w') as f:
            f.write(generate_tex(base_name, items, title))
            
        print(f"Generated {out_path}")

if __name__ == '__main__':
    main()
