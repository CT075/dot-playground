export TEXINPUTS:=$(TEXINPUTS):/home/cam/System/lib/latex

FILE := proof.tex

pdf: $(FILE)
	pdflatex $(FILE) && pdflatex $(FILE)

clean:
	rm *.pdf *.log *.aux *.out

