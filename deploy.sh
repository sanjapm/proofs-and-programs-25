set -e
./mk_imports.sh
lake build
cd docbuild
# rm -rf .lake/build/doc
lake build PfsProgs25:docs
rsync -avz .lake/build/doc/ gadgil@math.iisc.ac.in:~/public_html/PfsProgs25doc
cd ..
