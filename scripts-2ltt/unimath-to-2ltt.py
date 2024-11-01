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


def add_exo(word, prevword):
    # Avoid keywords and whitespace
    keywords = [
        "let",
        "in",
        "where",
        "```",
        "```agda",
        "```text",
        "{-#",
        "INLINE",
        "#-}",
        "open",
        "import",
        "module",
        "using",
        "renaming",
        "to",
        "public",
        ";",
        "hiding",
        "=",
        "_=_",
        ":",
        "→",
        "λ",
        "_",
        "⦃",
        "⦄",
        "Level",
        "lzero",
        "lsuc",
        "⊔",
        "_⊔_",
        "private",
        "abstract",
        "postulate",
        "primitive",
        "record",
        "data",
        "constructor",
        "field",
        "instance",
        "eta-equality",
        "no-eta-equality",
        "inductive",
        "pattern",
        "infix",
        "infixr",
        "infixl",
        "syntax",
        "do",
        "|",
        "...",
        "with",
    ]
    hardcodes = {
        "if_then_else_": "ifᵉ_thenᵉ_elseᵉ_",
        "_≡_mod_": "_≡ᵉ_modᵉ_",
        "@(n , f)": "@ᵉ(nᵉ ,ᵉ fᵉ)",
    }
    cleanword = word
    for char in ["(", ")", "{", "}", "."]:
        cleanword = cleanword.replace(char, "")

    if word in hardcodes:
        return hardcodes[word]

    if (
        (word in keywords)
        or (cleanword in keywords)
        or word.isspace()
        or all(char in "λ()}{[]" for char in word)
        or (represents_int(word) and prevword in ["infix", "infixl", "infixr"])
    ):
        return word

    for i in range(len(word) - 1, -1, -1):
        if word[i] not in "}]):_":
            return word[0 : i + 1] + "ᵉ" + word[i + 1 : len(word)]

    return word


def should_skip_line(line):
    lines_to_avoid = ["#", "<", "```", "{-# OPTIONS"]
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


def process_contents(contents):
    # Split and modify
    re_S = re.compile(r"(\S+)")
    in_agda_code = False
    has_nat = False
    lines = contents.splitlines()

    for line_n in range(len(lines)):
        line = lines[line_n]
        if in_agda_code:
            if line == "```":
                in_agda_code = False
                continue
            elif should_remove_line(line):
                lines[line_n] = (
                    ""  # TODO: This makes blank lines that should be removed
                )
            elif should_skip_line(line):
                # Nothing
                1
            else:
                words = re_S.split(line)
                for i in range(len(words)):
                    if (
                        i > 1
                        and represents_int(words[i])
                        and not (words[i - 2] in ["infix", "infixl", "infixr"])
                    ):
                        has_nat = True
                    words[i] = add_exo(words[i], "" if i < 2 else words[i - 2])
                lines[line_n] = "".join(words)
        else:
            if line == "```agda":
                in_agda_code = True
    updated_contents = "\n".join(lines)

    # Import nats if needed
    if has_nat:
        if (
            not "open import elementary-number-theory.natural-numbersᵉ"
            in updated_contents
        ):
            split_at = updated_contents.find("```agda\nopen import") + 8
            updated_contents = (
                updated_contents[0:split_at]
                + "open import elementary-number-theory.natural-numbersᵉ\n"
                + updated_contents[split_at : len(updated_contents)]
            )

    return updated_contents


def main():
    for filepath in glob.iglob(
        f"{agda_unimath_directory_path}/src/**/*.lagda.md", recursive=True
    ):
        # Read the file contents
        with open(filepath, "r") as file:
            contents = file.read()

        updated_contents = process_contents(contents)

        # Open the file in write mode (overwrites existing content)
        new_filepath = filepath[0 : len(filepath) - 9] + "ᵉ.lagda.md"
        with open(new_filepath, "w") as file:
            file.write(updated_contents)
            print(f"Updated {filepath}")

    # Modify universes, nats and flags
    os.system(
        f"cp {cwd}/scripts/universe-levelsᵉ.lagda.md {agda_unimath_directory_path}/src/foundation/universe-levelsᵉ.lagda.md"
    )
    # Hardcodes some natural number names
    os.system(
        f"cp {cwd}/scripts/natural-numbersᵉ.lagda.md {agda_unimath_directory_path}/src/elementary-number-theory/natural-numbersᵉ.lagda.md"
    )
    # This is so the inverses of a composition of equivalences computes
    os.system(
        f"cp {cwd}/scripts/equivalencesᵉ.lagda.md {agda_unimath_directory_path}/src/foundation-core/equivalencesᵉ.lagda.md"
    )
    os.system(
        f"cp {cwd}/scripts/agda-unimath.agda-lib {agda_unimath_directory_path}/agda-unimath.agda-lib"
    )

    os.system("cp -r agda-unimath/* agda-unimathᵉ")
    os.system("cd agda-unimathᵉ/src && find . | grep -v 'ᵉ'  | xargs rm -f")
    os.system("cd agda-unimathᵉ && git clean -f && git reset --hard")


main()
