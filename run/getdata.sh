
for a in mo/*.yaml if/*.yaml as/*.yaml
do
  uv run python3 ../hagent/step/v2chisel_pass1/v2chisel_pass1.py ${a} -o out/${a}  >out/${a}.stdout 2>out/${a}.stderr
done
