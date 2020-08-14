ISABELLE = isabelle
ifeq ($(AFP),)
	AFP_THYS = $$AFP
else
	AFP_THYS = $(AFP)/thys
endif

verimon:
	$(ISABELLE) build -ev -o "document=pdf" -d '$(AFP_THYS)' -D .

.PHONY: verimon
