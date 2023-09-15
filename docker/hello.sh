cd /root/caesar

echo
echo
echo "Welcome to Caesar's Docker container."
echo
echo "-------------------------------"
echo OOPSLA Artifact Evaluation Guide
echo
echo     See OOPSLA_AEC.md
echo 
echo "-------------------------------"
echo
echo "You are now in the project's main directory."
echo
echo "The benchmarks can be run with"
echo "    fish run-benchmarks.fish"
echo
echo "You can run caesar on individual files, e.g."
echo "    caesar tests/zeroconf.heyvl" 
echo 
echo "For usage information, run"
echo "    caesar --help"
echo 
echo "Online documentation is available on"
echo "    https://philipp15b.github.io/caesar/"

# we cannot use poetry shell, since that's bugged in virtualized environments
# where it for some reason cannot detect the current shell application and then
# just exits with an error. this is how I would have done it with `poetry
# shell`:
    # start a poetry shell, but do not show virtualenv clutter in the shell prompt 
    # export VIRTUAL_ENV_DISABLE_PROMPT=1
    # poetry shell --directory pgcl/pgcl2heyvl --quiet

# instead, use poetry run with bash.
# also to note: we have to run realpath ourselves, since poetry run fails to do
# so internally. it then simply adds the corresponding *relative* venv path to
# PATH, which is wrong as soon as the user switches a directory.
exec poetry --directory $(realpath pgcl/pgcl2heyvl) run bash
