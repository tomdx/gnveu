#include <sys/ioctl.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/queue.h>

#include <ctype.h>
#include <err.h>
#include <errno.h>
#include <event.h>
#include <fcntl.h>
#include <limits.h>
#include <netdb.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "log.h"

#define ET_OFFSET 12 /* Offset of the ethertype field in an ethernet frame */

#define IPV_6 6		/* IP Version 6 */
#define IPV_4 4		/* IP Version 4 */
#define IPV_ERR -1 	/* Not an IP version */
#define G_HEADER_SIZE 8 /* Number of bytes in a simple geneve header */

static int conn_socket;				/* socket for connection */
static struct sockaddr_storage *conn_addr;	/* sockaddr for connection */
static int conn_addrlen;			/* length of sockaddr */
static struct event *timeout_ev;		/* Timeout event */
static struct timeval timeout;			/* Timeout duration */

/*
 * Information relating to a geneve tunnel. Node of a linked list.
 */
struct tunnel {
	SLIST_ENTRY(tunnel) entry;	/* Next tunnel in list */
	struct	event ev;		/* Associated event */
	char   *tap;			/* Associated tap device */
	int	fd;			/* Tap device's file descriptor */
	int	vni;			/* Associated vni */	
};
SLIST_HEAD(tunnel_list, tunnel);

/*
 * Command line arguments
 */
struct args {
	struct	tunnel_list *tunnels;	/* List of tunnels */
	char   *src_address;		/* Local address to bind to */
	char   *src_port;		/* Local port to bind to */
	char   *dest_address;		/* Address to connect to */
	char   *dest_port;		/* Port to connect to */
	int	timeoutlen;		/* Length of timeout on tap device */
	bool	daemonise;		/* Whether to run as a daemon */
	sa_family_t	addr_family;	/* Address family */
};

static int	get_ipv(uint8_t *);
static uint8_t *unpack_header(uint8_t *, uint32_t *);
static void	init_header(uint8_t *, uint32_t);
static void	recv_packet(int, short, void *);
static void	send_packet(int, short, void *);
static void	bind_local(char *, char *, sa_family_t);
static void	parse_opts(struct args *, int *, char ***);
static void	get_conn_info(char *, char *, sa_family_t);
static void	timeout_exit(int, short, void *);
static void 	create_conn_event(struct tunnel_list *);
static void	create_tunnels(struct tunnel_list *);
static void	create_timeout(int);

__dead static void	usage(void);

/*
 * Print invalid usage error message
 */
__dead static void
usage(void)
{
	extern char *__progname;
	fprintf(stderr, "usage: %s [-46d] [-l address] [-p port] -t 120 \n"
	    "-e /dev/tapX@vni \n"
	    "server [port])\n", __progname);
	exit(1);
}

/*
 * Get the IP version in the payload of an ethernet frame.
 *
 * frame: Ethernet frame
 *
 * RETURN: IP version (4 or 6), or -1 if neither.
 */
static int
get_ipv(uint8_t *frame)
{
	/* 
	 * IPV4: 0x0800
	 * IPV6: 0x86DD
	 */
	if (frame[ET_OFFSET] == 0x08 && frame[ET_OFFSET + 1] == 0x00)
		return IPV_4;
	else if (frame[ET_OFFSET] == 0x86 && frame[ET_OFFSET + 1] == 0xDD)
		return IPV_6;
	return IPV_ERR;
}

/*
 * Initialises a simple geneve header with type ethernet, using a specified
 * VNI. This will occupy the first 8 bytes pointed to by the pointer.
 *
 * packet: Pointer to location to initialise header at
 * vni: Virutal network identifier to include in header
 */
static void
init_header(uint8_t *packet, uint32_t vni)
{
	/* Zero out version, opt len and reserved fields*/
	packet[0] = 0;
	packet[1] = 0;

	/* Protocol type: Ethernet */
	packet[2] = 0x65;
	packet[3] = 0x58;

	/* VNI */
	packet[4] = vni >> 16;
	packet[5] = (vni >> 8) & 0x00FF;
	packet[6] = vni & 0x00FF;

	/* Zero the reserved field */
	packet[7] = 0;
}

/*
 * Retrieve the VNI from a geneve header and return a pointer to the
 * underlying ethernet frame.
 *
 * packet: Geneve packet
 * vni: Variable to store the virtual network identifier
 *
 * RETURN: pointer to the underlying ethernet frame
 */
static uint8_t *
unpack_header(uint8_t *packet, uint32_t *vni)
{
	int optlen;
	uint16_t type;

	/* Make sure the protocol type is ethernet (0x6558) */
	type = (packet[2] << 8) + packet[3];
	if (type != 0x6558) {
		lwarnx("Invalid protocol type. Expected 0x6558, got %x", type);
		return NULL;
	}

	/* Get the length of additional options at the end of the header */
	optlen = (packet[0] >> 2) * 4;
	lwarnx("OPTLEN: %d", optlen);

	/* Get the VNI of the packet */
	*vni = (packet[4] << 16) + (packet[5] << 8) + packet[6];
	return packet + G_HEADER_SIZE + optlen; /* Start of ethernet packet */
}

/*
 * Callback function for EV_READ on the connection socket. Reads all bytes
 * from the socket, and extract the VNI from the geneve header. Send the
 * ethernet frame into the respective tap device (according to the vni).
 *
 * This function will reset the timeout when fired.
 *
 * fd: Connection socket
 * revents: Event which triggered the callback
 * args: List of tunnels
 */
static void
recv_packet(int fd, short revents, void *args)
{
	struct tunnel_list *tunnels;
	struct tunnel *tun;
	uint8_t *packet;
	void *frame;
	int vni, bytes_read, bytes, ip_version;

	tunnels = (struct tunnel_list *) args;

	/* Refresh timeout */
	if (evtimer_initialized(timeout_ev)) {
		evtimer_del(timeout_ev);
		evtimer_add(timeout_ev, &timeout);
	}

	if (ioctl(fd, FIONREAD, &bytes) == -1)
		lwarn("recv_packet(): icoctl failed");

	packet = calloc(bytes + 10000, sizeof(uint8_t));
	bytes_read = read(fd, packet, bytes + 10000);

	/* Remove the header */
	frame = unpack_header(packet, &vni);
	if (frame == NULL)
		return;

	/* Filter IP versions for specific VNIs */
	ip_version = get_ipv(frame);
	if (vni == 4096 && ip_version != IPV_4) {
		free(packet);
		lwarnx("FILTERED recv: Not IPV4 (IPV: %d)", ip_version);
		return;
	} else if (vni == 8192 && ip_version != IPV_6) {
		free(packet);
		lwarnx("FILTERED recv: Not IPV6 (IPV: %d)", ip_version);
		return;
	}
	lwarnx("recv_packet(): bytes: %d, bytes_read: %d, ipv: %d, vni: %d",
	    bytes, bytes_read, ip_version, vni);

	/* Send the ethernet frame to the corresponding tap device */
	SLIST_FOREACH(tun, tunnels, entry) {
		if (tun->vni == vni) {
			lwarnx("Writing into: %s", tun->tap);
			if (write(tun->fd, frame, bytes - G_HEADER_SIZE) == -1)
				lwarn("Write failed");
		}
	}

	free(packet);
}

/*
 * Callback function for EV_READ or EV_TIMEOUT on tap device file descriptors.
 * If called via EV_TIMEOUT, terminate the program and print an error message.
 * If called via EV_READ, read all bytes from the associated tap device, wrap
 * it in a geneve header and send the packet into the connection socket.
 *
 * This function will reset the timeout when fired.
 *
 * fd: File descriptor to read from
 * revents: Event that triggered the callback
 * conn: Tunnel associated with the fd
 */
static void
send_packet(int fd, short revents, void *conn)
{
	struct tunnel *tunnel;
	uint8_t *buffer;
	int bytes, bytes_read, ip_version, error;

	/* Refresh timeout */
	if (evtimer_initialized(timeout_ev)) {
		evtimer_del(timeout_ev);
		evtimer_add(timeout_ev, &timeout);
	}

	tunnel = conn;

	if (ioctl(fd, FIONREAD, &bytes) == -1)
		lwarn("send_packet(): ioctl failed");
	buffer = calloc(bytes + G_HEADER_SIZE + 10000, sizeof(uint8_t));
	bytes_read = read(fd, buffer + G_HEADER_SIZE, bytes + 10000);

	/* Filter IP version for certain VNIs */
	ip_version = get_ipv(buffer + G_HEADER_SIZE);
	if (tunnel->vni == 4096 && ip_version != IPV_4) {
		free(buffer);
		lwarnx("FILTERED send: Not IPV4 (IPV: %d)", ip_version);
		return;
	} else if (tunnel->vni == 8192 && ip_version != IPV_6) {
		free(buffer);
		lwarnx("FILTERED send: Not IPV6 (IPV: %d)", ip_version);
		return;
	}
	lwarnx("send_packet(): bytes: %d, bytes_read %d, ipv: %d, vni: %d, ta"
	    "p: %s", bytes, bytes_read, ip_version, tunnel->vni, tunnel->tap);

	init_header(buffer, tunnel->vni);

	/* Send packet to the connection socket */
	error = sendto(conn_socket, buffer, G_HEADER_SIZE + bytes_read, 0,
	    (struct sockaddr *)conn_addr, conn_addrlen);
	if (error == -1)
		lwarn("sendto() FAILED");

	free(buffer);

}

/*
 * Bind the global connection socket to a local address and port.
 *
 * address: Local address to bind to
 * port: Local port to bind to
 * addr_family: Address family 
 */
static void
bind_local(char *address, char *port, sa_family_t addr_family)
{
	struct addrinfo hints, *res, *res0;
	int error;

	memset(&hints, 0, sizeof(hints));
	hints.ai_family = addr_family;
	hints.ai_socktype = SOCK_DGRAM;
	hints.ai_flags = AI_PASSIVE;

	error = getaddrinfo(address, port, &hints, &res0);
	if (error != 0)
		lerrx(1, "%s", gai_strerror(error));

	for (res = res0; res; res = res->ai_next) {
		error = bind(conn_socket, res->ai_addr, res->ai_addrlen);
		if (error == -1)
			continue;
		break;
	}
	if (error == -1)
		lerr(1, "Error: Bind failed");
	freeaddrinfo(res0);
}

/*
 * Get an ai_addr struct and the ai_addrlen of the host to connect to, and
 * store it in the global variables. Exits with an error code of 1 if the
 * addrinfo could not be found.
 *
 * address: Host address
 * port: Host port
 * addr_family: Address family (AI_INET or AI_INET6)
 */
static void
get_conn_info(char *address, char *port, sa_family_t addr_family)
{
	struct addrinfo hints, *res;
	int error;
	
	memset(&hints, 0, sizeof(hints));
	hints.ai_family = addr_family;
	hints.ai_socktype = SOCK_DGRAM;
	error = getaddrinfo(address, port, &hints, &res);
	if (error != 0)
		lerrx(1, "Cannot connect to host: %s", gai_strerror(error));

	conn_addr = (struct sockaddr_storage *) (res->ai_addr);
	conn_addrlen = res->ai_addrlen;

}

/*
 * Terminate the program (called upon timing out).
 */
static void
timeout_exit(int fd, short revents, void *arg)
{
	lerrx(1, "TIMEOUT");
}

/*
 * Create, set and add an event that is triggered when bytes are available on
 * the global connection file descriptor.
 *
 * tunnels: List of tunnels
 */
static void 
create_conn_event(struct tunnel_list *tunnels)
{
	struct event *recv_ev;

	recv_ev = calloc(1, sizeof(struct event));
	recv_ev->ev_fd = conn_socket;
	event_set(recv_ev, EVENT_FD(recv_ev),
	    EV_READ | EV_PERSIST, recv_packet, tunnels);
	event_add(recv_ev, NULL);

}

/*
 * Create, set and add an event for each tunnel (file descriptor pointing to
 * tap device), with an appropriate timeout length (no timeout if negative).
 * This event will fire when bytes become available from the file descriptor. 
 *
 * tunnels: List of tunnels to create.
 */
static void
create_tunnels(struct tunnel_list *tunnels)
{
	struct tunnel *tun;
	int tap_fd;

	SLIST_FOREACH(tun, tunnels, entry) {
		tap_fd = open(tun->tap, O_RDWR | O_NONBLOCK);
		if (tap_fd == -1)
			lerr(1, "Could not open TAP - %s", tun->tap);
		tun->ev.ev_fd = tap_fd;
		tun->fd = tap_fd;
		event_set(&(tun->ev), EVENT_FD(&(tun->ev)),
		    EV_READ | EV_PERSIST, send_packet, tun);

		event_add(&(tun->ev), NULL);
	}
}

/*
 * Create, set and add timeout event, with a specified timeout length. The
 * event will be stored in in the timeout_ev global and the timeval struct will
 * be stored in the timeout global. If timeoutlen is less than 0, the timeout
 * will be disabled. In this circumstance, timeout_ev is allocated but not
 * initialised - this allows the evtimer_initialized function to determine
 * whether there is a timeout set.
 *
 * timeoutlen: Length of timeout in seconds.
 */
static void
create_timeout(int timeoutlen)
{
	timeout_ev = calloc(1, sizeof(struct event));
	if (timeoutlen > 0) {
		evtimer_set(timeout_ev, timeout_exit, NULL);
		timeout.tv_sec = timeoutlen;
		timeout.tv_usec = 0;
		evtimer_add(timeout_ev, &timeout);
	}
}

/*
 * Parse the command line options from argc and argv into a struct.
 * Args:
 *
 * args: struct to store the command line aguments in
 */
static void
parse_opts(struct args *args, int *argc, char ***argv)
{
	const char *errmsg;
	struct tunnel *tun; 
	char *sep;
	int opt;
	bool no_tunnel;

	errmsg = NULL;
	no_tunnel = true;
	/* Default values */
	args->src_address = NULL;
	args->src_port = NULL;
	args->dest_port = "6081"; /* Default port */
	args->timeoutlen = 0;
	args->addr_family = AF_INET;
	args->daemonise = true;

	while ((opt = getopt(*argc, *argv, "46dl:p:t:e:")) != -1) {
		switch(opt) {
		case '4':
			args->addr_family = AF_INET;
			break;
		case '6':
			args->addr_family = AF_INET6;
			break;
		case 'd':
			args->daemonise = false;
			break;
		case 'l':
			args->src_address = optarg;
			break;
		case 't':
			args->timeoutlen = strtonum(optarg, INT_MIN, INT_MAX,
			    &errmsg);
			break;
		case 'p':
			args->src_port = optarg;
			break;
		case 'e':
			no_tunnel = false;
			tun = calloc(1, sizeof(struct tunnel));
			tun->tap = optarg;
			sep = strchr(optarg, '@');
			if (sep == NULL)
				usage();
			*sep = '\0';
			tun->vni = strtonum(sep + 1, 0, INT_MAX, &errmsg);
			SLIST_INSERT_HEAD(args->tunnels, tun, entry);
			break;
		default:
			usage();
			/* NOTREACHED */
		}
		if (errmsg != NULL)
			usage();
	}
	*argc -= optind;
	*argv += optind;

	if (*argc == 2)
		args->dest_port = (*argv)[1];
	else if (*argc != 1)
		usage();

	args->dest_address = (*argv)[0];

	if (args->timeoutlen == 0)
		usage();
	if (no_tunnel)
		usage();
}

/*
 * Connects to a host via a port, and establishes a number of geneve tunnels
 * each with a unique VNI. Any ethernet frames written to the specific tap
 * devices are encapsulated in a geneve header and sent to the connection.
 * Any incoming geneve packets from the connection are decapsulated and the
 * underlying ethernet frame is sent through the specified tap device
 * (as specified by the VNI in the header).
 */
int
main(int argc, char **argv)
{
	struct args args;
	struct tunnel_list tunnels = SLIST_HEAD_INITIALIZER(tunnels);

	args.tunnels = &tunnels;
	parse_opts(&args, &argc, &argv);
	if (args.daemonise) {
		logger_syslog(getprogname());
		if (daemon(1, 1) == -1)
			lerr(1, "Daemonise failed");
	}
	conn_socket = socket(args.addr_family, SOCK_DGRAM, IPPROTO_UDP);

	event_init();

	get_conn_info(args.dest_address, args.dest_port, args.addr_family);

	create_conn_event(args.tunnels);

	if (args.src_address != NULL) {
		if (args.src_port == NULL)
			args.src_port = args.dest_port;
		bind_local(args.src_address, args.src_port, args.addr_family);
	}

	create_tunnels(args.tunnels);
	create_timeout(args.timeoutlen);
	
	event_dispatch();
}

