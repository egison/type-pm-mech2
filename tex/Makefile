TARGET = type-pm-mech2-guide
TEXMFVAR ?= /tmp/type-pm-mech2-texmf-var
export TEXMFVAR

.PHONY: all clean cleanAll

all: $(TARGET).pdf

$(TARGET).pdf: $(TARGET).tex
	mkdir -p $(TEXMFVAR)
	lualatex -interaction=nonstopmode -halt-on-error -jobname=$(TARGET) $(TARGET).tex
	lualatex -interaction=nonstopmode -halt-on-error -jobname=$(TARGET) $(TARGET).tex

clean:
	rm -f $(TARGET).aux $(TARGET).log $(TARGET).out $(TARGET).toc

cleanAll: clean
	rm -f $(TARGET).pdf
