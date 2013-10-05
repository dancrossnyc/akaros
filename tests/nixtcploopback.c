/* ping for ip v4 and v6 */
#include <stdlib.h>
#include <stdio.h>
#include <parlib.h>
#include <unistd.h>
#include <signal.h>
#include <nixip.h>
#include <icmp.h>
#include <ctype.h>

/* see http://swtch.com/plan9port/man/man3/dial.html */
void caller(char *addr)
{
	char data[512];
	int fd = dial(addr, 0, 0, 0);
	while (1){
		int amt;
		amt = read(0, data, sizeof(data));
		if (amt <= 0)
			break;
		write(fd, data, amt);
		amt = read(fd, data, sizeof(data));
		if (amt <= 0)
			break;
		write(1, data, amt);
	}
}

int server(char *addr)
{
	int dfd, acfd, lcfd;
	char adir[40], ldir[40];
	int n;
	char buf[256];
	acfd = announce(addr, adir);
	if (acfd < 0)
		return -1;
	for (;;) {
/* listen for a call */
		lcfd = listen(adir, ldir);
		if (lcfd < 0)
			return -1;
/* fork a process to echo */
		switch (fork()) {
				case -1:
				perror("forking");
				exit(1);
				break;
			case 0:
/* accept the call and open the data file */
				dfd = accept(lcfd, ldir);
				if (dfd < 0)
					return -1;
/* echo until EOF */
				while ((n = read(dfd, buf, sizeof(buf))) > 0)
					write(dfd, buf, n);
				exit(0);
			default:
				close(lcfd);
				break;
		}
	}
}

void main(int argc, char **argv)
{
	int fd, msglen, interval, nmsg;
	char *ds;
	int pid;

	pid = fork();
	if (pid < 0) {
		perror("fork");
		exit(1);
	}
	if (pid == 0)
		caller(argv[2]);
	server(argv[1]);
}
