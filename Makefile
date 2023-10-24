.PHONY: test check fmt coverage

test:
	./test_doc.py && ./test_unit.py

check:
	pyright ./cvc5_pythonic_api

fmt:
	black --required-version 23.7.0 ./cvc5_pythonic_api

check-fmt:
	black --check --verbose --required-version 23.7.0 ./cvc5_pythonic_api

coverage:
	coverage run test_unit.py && coverage report && coverage html
