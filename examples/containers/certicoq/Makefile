
all: a.out


libs:
	(cd base; make)
	(cd lib; make)

intset_bench_j.main.c: libs
	coqc -R lib "" -R base "" intset_bench_j.v

a.out: intset_bench_j.main.c  gc.c main.c
	gcc -m32 -O2 main.c gc.c intset_bench_j.main.c 

clean:
	(cd base; make clean)
	(cd lib; make clean)
	rm -f *.vo *.glob intset_test.mli intset_test.ml intset_bench_j.main.c Top.main.c a.out



