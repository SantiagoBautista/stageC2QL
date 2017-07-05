default: all clean

all: build

build:
	pdflatex rapport.tex
	biber rapport.bcf
	pdflatex rapport.tex

clean:
	rm -f rapport.aux rapport.log rapport.bcf rapport.run.xml rapport.syntex.gz
