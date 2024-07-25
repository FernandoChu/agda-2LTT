import re
import glob
import os

# This file should be run from the root folder

cwd = os.getcwd()
agda_unimath_directory_path = f"{cwd}/agda-unimath"

def represents_int(s):
    try:
        int(s)
    except ValueError:
        return False
    else:
        return True

def add_exo(word):
    # Avoid keywords and whitespace
    keywords = ["let", "in", "where", "```", "```agda", "```text", "{-#", "INLINE", "#-}", "open", "import", "module", "using", "renaming", "to", "public", ";", "hiding", "=", ":", "→","λ", "_", "._", "Level", "Level)", "Level}", "lzero", "lsuc", "(lsuc", "lzero)", "⊔", "private", "abstract", "record", "data", "constructor", "field", "instance", "eta-equality", "no-eta-equality", "inductive", "pattern", "infix", "infixr", "infixl", "syntax", "postulate", "primitive", "do", "|", "...", "with"]
    if (word in keywords) or word.isspace() or all(char in "λ()}{[]" for char in word) or represents_int(word):
        return word
    
    if (word == "0"):
        return "zero-ℕᵉ"

    for i in range(len(word) - 1, -1, -1):
       if word[i] not in "}]):_":
           return word[0:i+1] + "ᵉ" + word[i+1:len(word)]

    return word

def should_skip_line(line):
    lines_to_avoid = ["#", "<", "```"]
    for start in lines_to_avoid:
        if line.startswith(start):
            return True
    return False

def should_remove_line(line):
    lines_to_avoid = ["{-# BUILTIN"]
    for start in lines_to_avoid:
        if line.startswith(start):
            return True
    return False

for filepath in glob.iglob(f"{agda_unimath_directory_path}/src/**/*.lagda.md", recursive=True):
    # Read the file contents
    with open(filepath, 'r') as file:
        contents = file.read()

    # TODO: The script should parse md and just modify the codeblocks
    # Split and modify
    re_S = re.compile(r'(\S+)')
    lines = contents.splitlines()
    for line_n in range(len(lines)):
        line = lines[line_n]
        if should_remove_line(line):
            lines[line_n] = '' # TODO: This can create two \n
        elif should_skip_line(line):
            # Nothing
            1
        else:
            words = re_S.split(line)
            for i in range(len(words)):
                words[i] = add_exo(words[i])
            lines[line_n] = ''.join(words)
    updated_contents = '\n'.join(lines)

    # Open the file in write mode (overwrites existing content)
    new_filepath = filepath[0:len(filepath)-9] + "ᵉ.lagda.md"
    with open(new_filepath, 'w') as file:
       file.write(updated_contents)
       print(f"Updated {filepath}")

# Modify universes
with open(f"{cwd}/scripts/universe-levelsᵉ.lagda.md", 'r') as file:
    contents = file.read()
with open(f"{agda_unimath_directory_path}/src/foundation/universe-levelsᵉ.lagda.md", 'w') as file:
    file.write(contents)

# Modify Flags
with open(f"{cwd}/scripts/agda-unimath.agda-lib", 'r') as file:
    contents = file.read()
with open(f"{agda_unimath_directory_path}/agda-unimath.agda-lib", 'w') as file:
    file.write(contents)