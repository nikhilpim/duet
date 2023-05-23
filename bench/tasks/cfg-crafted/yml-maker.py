import os

TEMPLATE = """format_version: '1.0'

input_files: '{}'

properties:
  - property_file: ../properties/unreach-call.prp
    expected_verdict: true\n"""

# set the directory path
directory = "."

# loop through all the files in the directory
for filename in os.listdir(directory):
    if filename.endswith(".c"):
        # create a new .yml filename
        yml_filename = os.path.splitext(filename)[0] + ".yml"
        # create the new file and write the template text to it
        with open(os.path.join(directory, yml_filename), "w") as f:
            f.write(TEMPLATE.format(filename))