
final.yaml: tmp.yaml
	poetry run python3 ../hagent/step/replicate_code/replicate_code.py -o final.yaml tmp.yaml

tmp.yaml: input.yaml
	poetry run python3 ../hagent/step/trivial/trivial.py -o tmp.yaml input.yaml

