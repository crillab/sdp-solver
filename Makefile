STANDARD := -std=c++20

CADICAL_INC := cadical/src/
CADICAL_LIB_DIR := cadical/build/
CADICAL_LIB := -lcadical
GQR_INC := gqr/gqr/
GQR_LIB_DIR := gqr/
GQR_LIB := -lgqr
PUGIXML_SRC := pugixml.cpp
PUGIXML_INC := .
SDP_INC := include

all: 

gen_tar: src/*.cpp include/*.hpp Makefile
	mkdir flexible && mkdir flexible/src && cp src/*.cpp flexible/src && mkdir flexible/include && cp include/*.hpp flexible/include && cp Makefile flexible && tar -cvf flexible.tar flexible && rm -rf flexible

types: main.o pog.o types.o variables.o constraints.o graphs.o sat.o rcc.o
	g++ $(STANDARD) -o $@ $^ ${PUGIXML_SRC} -L${CADICAL_LIB_DIR} ${CADICAL_LIB} 	
	rm *.o

prof: main.o pog.o types.o variables.o constraints.o graphs.o sat.o
	g++ $(STANDARD) -o $@ $^ ${PUGIXML_SRC} -pg -L${CADICAL_LIB_DIR} ${CADICAL_LIB}
	rm *.o

main.o: src/main.cpp
	g++ $(STANDARD) -I${SDP_INC} -I${CADICAL_INC} -c $< -o $@

sat.o: src/sat.cpp
	g++ ${STANDARD} -I${SDP_INC} -I${CADICAL_INC} -c $< -o $@

rcc.o: src/rcc.cpp
	g++ ${STANDARD} -I${SDP_INC} -I${CADICAL_INC} -c $< -o $@
	# GQR requires LD_LIBRARY_PATH to be set to GQR_LIB_DIR

graphs.o: src/graphs.cpp
	g++ $(STANDARD) -I${SDP_INC} -I${CADICAL_INC}  -c $< -o $@

pog.o: src/pog.cpp
	g++ $(STANDARD) -I${SDP_INC} -I${PUGIXML_INC} -I${CADICAL_INC} -c $< -o $@

constraints.o: src/constraints.cpp
	g++ $(STANDARD) -I${SDP_INC} -I${PUGIXML_INC} -I${CADICAL_INC} -c $< -o $@

variables.o: src/variables.cpp
	g++ $(STANDARD) -I${SDP_INC} -I${PUGIXML_INC} -I${CADICAL_INC} -c $< -o $@

types.o: src/types.cpp
	g++ $(STANDARD) -I${SDP_INC} -I${CADICAL_INC} -I${PUGIXML_INC} -c $< -o $@

clean:
	rm -f *.o *~ types prof gmon.out
