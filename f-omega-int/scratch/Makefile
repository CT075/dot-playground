export TEXINPUTS:=$(TEXINPUTS)

FILE := scratch.tex

pdf: $(FILE)
	pdflatex $(FILE) && pdflatex $(FILE)

clean:
	rm *.pdf *.log *.aux *.out

