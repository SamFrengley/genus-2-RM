"""
This short python script rewrites a few variable names in several Magma files to
ensure that our intrinsics can be run in a directory independent fashion.

To run this file requires Python 3.10 and is untested on all but Unix systems.

TO RUN, YOU NEED TO BE IN THE DIRECTORY OF THIS FILE OR THIS SCRIPT WILL FAIL.
"""

import os

def rewrite_first_line(my_file, new_line):
    """
    Rewrites the first line of a file

    Parameters
    ----------
    my_file str
        The file to edit.
    new_line str
        The new string to become the first line.

    Returns
    -------
    None
    """
    with open(my_file, "r") as f:
        lines = f.readlines()

    if lines:
        lines[0] = new_line

    with open(my_file, "w") as f:
        f.writelines(lines)    


def new_models(main_dir):
    """
    Changes the file `models/weierstrass.m` to have a correct first line
    
    Parameters
    ----------
    main_dir str
        The directory of this file, the parent directory of 
        `models/weierstrass.m`.
    
    Returns
    -------
    None
    """
    new_line = f'CURR_DIR := "{main_dir}/models/";\n'
    my_files = [
        f"{main_dir}/models/weierstrass.m",
        f"{main_dir}/models/get-polynomials.m",
        f"{main_dir}/models/invariants.m"
    ]
    for my_file in my_files:
        rewrite_first_line(my_file, new_line)
    
    
def main():
    """Main function"""
    main_dir = os.getcwd()
    new_models(main_dir)

if __name__ == "__main__":
    main()
