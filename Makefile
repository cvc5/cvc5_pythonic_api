.PHONY: test check fmt coverage

test:
	./z3doc_test.py && ./z3test.py

check:
	pyright ./cvc5_z3py_compat

fmt:
	black ./cvc5_z3py_compat

coverage:
	coverage run z3test.py && coverage report && coverage html
