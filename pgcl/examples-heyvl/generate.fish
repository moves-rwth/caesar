echo Generating HeyVL files from the examples directory...

cd (dirname (status -f))
cd ../pgcl2heyvl

# in the docker container, we have seen the command poetry run pgcl2heyvl fail
# when already inside a virtual environment. It said that there's no such file
# or directory 'python'. I have no idea how to debug this, so we'll just test
# once if the command works and otherwise just hope that pgcl2heyvl is globally
# available already (because we're in a venv).
set -l pgcl2heyvl
if poetry run pgcl2heyvl --help &> /dev/null
    set pgcl2heyvl poetry run pgcl2heyvl
else 
    set pgcl2heyvl pgcl2heyvl
end 

for file in ../examples/*.pgcl; 
    echo Translating (basename $file)
    $pgcl2heyvl $file > ../examples-heyvl/(basename -s .pgcl $file).heyvl;
end
