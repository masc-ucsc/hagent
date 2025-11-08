final.yaml: intermediate.yaml
	uv run python ../hagent/step/replicate_code/replicate_code.py -o final.yaml intermediate.yaml

intermediate.yaml: tmp.yaml
	uv run python ../hagent/step/replicate_code/replicate_code.py -o intermediate.yaml tmp.yaml

tmp.yaml: input.yaml
	uv run python ../hagent/step/trivial/trivial.py -o tmp.yaml input.yaml

clean:
	rm tmp.yaml
	rm intermediate.yaml
	rm final.yaml
	rm -rf equiv_check_*
