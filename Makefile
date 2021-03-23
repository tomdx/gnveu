PROG=gnveu
SRCS=gnveu.c log.c
LDADD=-levent
DPADD=${LIBEVENT}
CFLAGS+=-Wall
DEBUG=-g
MAN=

.include <bsd.prog.mk>
