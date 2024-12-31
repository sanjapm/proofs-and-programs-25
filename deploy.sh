set -e
lake build
cd docbuild
lake build PfsProgs25:docs
rsync -avz .lake/build/doc/ gadgil@math.iisc.ac.in:~/public_html/PfsProgs25doc
cd ..
