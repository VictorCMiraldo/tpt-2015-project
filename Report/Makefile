CODE_AGDA_STDLIB=/home/victor/Documents/UU/Thesis/agda-stdlib/src
CODE_AGDA_REL=/home/victor/Documents/UU/Thesis/msc-agda-tactics/Agda
CODE_AGDA_PRELUDE=/home/victor/Documents/UU/Thesis/msc-agda-tactics/Agda/stdlib-extensions
CODE_AGDA_RW=/home/victor/Documents/UU/Thesis/agda-rw
CODE_AGDA_PROJ=/home/victor/Documents/UU/TPT/2015/tpt-2015-project

all: report.tex latex/Excerpts.tex latex/PMapParts.tex
	vtex report.tex
		
latex/Excerpts.tex: Excerpts.lagda
	agda --allow-unsolved-metas -i $(CODE_AGDA_STDLIB) -i . \
		-i $(CODE_AGDA_REL) -i $(CODE_AGDA_PRELUDE) -i $(CODE_AGDA_RW) \
		-i $(CODE_AGDA_PROJ) --latex Excerpts.lagda
		
latex/PMapParts.tex: PMapParts.lagda
	agda --allow-unsolved-metas -i $(CODE_AGDA_STDLIB) -i . \
		-i $(CODE_AGDA_REL) -i $(CODE_AGDA_PRELUDE) -i $(CODE_AGDA_RW) \
		-i $(CODE_AGDA_PROJ) --latex PMapParts.lagda
