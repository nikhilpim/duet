import os

directory = "."
set_name = "recursivesafe-supreme.set"
# loop through all the files in the directory

with open(os.path.join(directory, set_name), "w") as f: 
    for filename in os.listdir(directory):
        if filename.endswith(".yml"):
            # create the new file and write the template text to it
                f.write("recursivesafe-supreme/"+filename+"\n")