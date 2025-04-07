EXECNAME := servois2

all:
	dune build
	mv run.exe $(EXECNAME)

clean:
	dune clean
	rm -f $(EXECNAME)

test: all
	python ./test.py ./$(EXECNAME)
