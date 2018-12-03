CC=gcc
CFLAGS=-Iincludes -Wall -Wextra -Wformat -ansi -std=c99 -pedantic
SRCDIR=src
OBJDIR=target
OBJS=$(OBJDIR)/mml/scanner.o \
	$(OBJDIR)/mml/token.o \
	$(OBJDIR)/defs.o
TESTS=test/mml/token_test.c \
	  test/mml/scanner_test.c

$(OBJDIR)/%.o : $(SRCDIR)/%.c includes/%.h
	$(CC) $(CFLAGS) -c $< -o $@

compile: $(OBJS)
# compile AND run the unit tests
test: compile
	$(CC) $(CFLAGS) test/runner.c test/test.c $(TESTS) $(OBJS) -o tests
	./tests
# remove everything, if they exist
clean:
	-rm -f $(OBJDIR)/*.o
	-rm -f $(OBJDIR)/*/*.o
	-rm -f tests
