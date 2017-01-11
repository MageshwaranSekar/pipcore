#include <stdint.h>
#include <pip/fpinfo.h>
#include <pip/api.h>
//#include <pip/debug.h>
#include <pip/vidt.h>
#include "eth.h"
#include "debug.h"
#include "galileo-support.h"


#include "pico_stack.h"
#include "pico_ipv4.h"
#include "pico_icmp4.h"
#include "pico_dev_galileo.h"
#include "custom_memalloc.h"

#define NUM_PING 10
#define HEAPSIZE 200000
uint8_t rpacket[IP_BUFSIZE];
static int finished = 0;
static char ch[HEAPSIZE];

INTERRUPT_HANDLER(asmInterrupt33,interrupt33)
    vcli();
    printf("MULTIPLEXER GOT INTERRUPT 33\n");
    vsti();
    viret();
    END_OF_INTERRUPT
INTERRUPT_HANDLER(asmInterrupt40,interrupt40)
    vcli();
    printf("MULTIPLEXER GOT INTERRUPT 40\n");
    vsti();
    viret();

    END_OF_INTERRUPT
INTERRUPT_HANDLER(asmInterrupt44,interrupt44)

    END_OF_INTERRUPT


INTERRUPT_HANDLER(asmInterrupt14,interrupt14)
    vcli();
    for(;;);
    END_OF_INTERRUPT

INTERRUPT_HANDLER(asmInterrupt15,interrupt15)
    vcli();
    for(;;);
    END_OF_INTERRUPT


void printPacket (void * buffer) {
    unsigned int size = IP_BUFSIZE;
    printf("\n***********\nNew Packet holding %d bytes of data %p\n***********\n", size, buffer);
    char *c;
    int counter=0;
    int i;
    for (i=2; i<size+2; i++) {
        c = (char *)buffer+i;
        if ( *c != '\0' ) {
            printf("%2x ", *c);
            counter++;
        }
        else {
            return;
        }
    }
}


/*uint8_t packet[68] = {  0x55,0x55,0x55,0x55,0x55,0x55,0x55,0xD5,0xff,0xff,0xff,0xff,0xff,0xff,0x98,0x4f,
                        0xee,0x05,0x64,0x32,0x08,0x06,0x00,0x01,0x08,0x00,0x06,0x04,0x00,0x01,0x98,0x4f,
                        0xee,0x05,0x64,0x32,0xC0,0xa8,0x00,0x0b,0x00,0x00,0x00,0x00,0x00,0x00,0xC0,0xa8,
                        0x00,0x0a,0x06,0x01,0x04,0x00,0x00,0x00,0x00,0x02,0x01,0x00,0x03,0x02,0x00,0x00,
                        0x05,0x01,0x03,0x01};
*/


/* gets called when the ping receives a reply, or encounters a problem */
void cb_ping(struct pico_icmp4_stats *s)
{
    char host[30];
    pico_ipv4_to_string(host, s->dst.addr);
    if (s->err == 0) {
        /* if all is well, print some pretty info */
        printf("%lu bytes from %s: icmp_req=%lu ttl=%lu time=%lu ms\n", s->size,
                host, s->seq, s->ttl, (long unsigned int)s->time);
        if (s->seq >= NUM_PING)
            finished = 1;
    } else {
        /* if something went wrong, print it and signal we want to stop */
        printf("PING %lu to %s: Error %d\n", s->seq, host, s->err);
        finished = 1;
    }
}
void main(pip_fpinfo* bootinfo){
		int id;
    struct pico_ip4 ipaddr, netmask;
    struct pico_device* dev;
		init_heap(ch, HEAPSIZE);


		initGalileoSerialPort(DEBUG_SERIAL_PORT);


    /* initialise the stack. Super important if you don't want ugly stuff like
     * segfaults and such! */
    pico_stack_init();
		
    /* create the tap device */
    dev = pico_eth_create("eth0");
    if (!dev) DEBUG(ERROR,"Error in pico_eth_create\n");
        //return -1;

    /* assign the IP address to the tap interface */
    pico_string_to_ipv4("10.0.0.2", &ipaddr.addr);
    pico_string_to_ipv4("255.255.255.0", &netmask.addr);
    pico_ipv4_link_add(dev, ipaddr, netmask);

    
    id = pico_icmp4_ping("10.0.0.1", NUM_PING, 1000, 10000, 64, cb_ping);
		//printf("starting ping\n");
    if (id == -1) DEBUG(ERROR,"ping error\n");
        //return -1;


    while (finished != 1){
		//while(1){
				pico_stack_tick();
				PICO_IDLE();
    }

    //printf("finished !\n");


    //registerInterrupt(33, &interrupt33, (uint32_t*)0x1000000);
    //registerInterrupt(40, &interrupt40, (uint32_t*)0x2000000);
    //registerInterrupt(14, &interrupt14, (uint32_t*)0x3000000);
    //registerInterrupt(15, &interrupt15, (uint32_t*)0x4000000);

    //vsti();
    //printf("HELLO FROM USERLAND\n");
    //quarkX1000_eth_init();
    //uint32_t time = pip_time();
    //DEBUG(TRACE,"TIME : %d\n",time);
    //send(packet,68);
    for(;;);
        //printf("Time : %d\n",pip_time());


}
