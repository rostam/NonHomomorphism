import sys

def generate_output_file(f1_path, f2_path, output_file_name):
    # Read the contents of f2 into a set for faster lookup
    with open(f2_path, 'r') as f2:
        f2_lines = set(f2.readlines())

    cnt = 0
    # Write lines from f1 that are not in f2 to the output file
    with open(f1_path, 'r') as f1, open(output_file_name, 'w') as output:
        for line in f1:
            if line not in f2_lines:
                cnt = cnt + 1
                output.write(line)

    print(f"The output with {cnt} lines has been saved to {output_file_name}.")

if __name__ == "__main__":
    if len(sys.argv) != 4:
        print("Usage: python script_name.py <f1_filename> <f2_filename> <output_filename>")
        sys.exit(1)

    f1_path = sys.argv[1]
    f2_path = sys.argv[2]
    output_file_name = sys.argv[3]

    generate_output_file(f1_path, f2_path, output_file_name)
