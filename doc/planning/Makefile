
SOURCES = milestones-shell.dot

OUTPUTS = milestones-shell.png milestones-shell.pdf

%.png: %.dot
	dot -Tpng $< -o$@
%.pdf: %.dot
	dot -Tpdf $< -o$@

all: $(OUTPUTS) $(SOURCES)

