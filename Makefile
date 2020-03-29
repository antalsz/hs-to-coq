all:
	make -C base
	make -C base-thy
	make -C examples/containers/lib

clean:
	make -C base clean
	make -C base-thy clean
	make -C examples/containers/lib clean
