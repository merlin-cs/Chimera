def format_smt_string(smt_string):
    """Cleans up an SMT-LIB string by removing redundant whitespace and empty lines."""
    lines = smt_string.split('\n')
    # Strip whitespace from each line and remove empty lines
    stripped_lines = [line.strip() for line in lines if line.strip()]
    # Join lines with a single newline, which is standard
    return '\n'.join(stripped_lines)
