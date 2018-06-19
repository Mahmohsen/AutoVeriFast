#include "dummy_protocol.h"
#include "stdlib.h"

#define APP_RECEIVE_PORT 121212

void send()
  //@ requires [?f0]world(dummy_pub); 
  //@ ensures  [f0]world(dummy_pub);
{
    struct network_status *net_stat = 
                                 network_connect("localhost", APP_RECEIVE_PORT);
    
    char i;
    struct item *m = create_data_item_from_char(i);
    //@ assert item(m, ?data, dummy_pub);
    //@ get_info_for_item(data);
    //@ close dummy_pub(data);
    //@ leak dummy_pub(data);
    network_send(net_stat, m);
    item_free(m);
    
    network_disconnect(net_stat);
}

struct item *receive()
  //@ requires [?f0]world(dummy_pub); 
  /*@ ensures  [f0]world(dummy_pub) &*& item(result, ?msg, dummy_pub) &*& 
               msg == data_item(_); @*/
{
    struct network_status *net_stat = network_bind_and_accept(APP_RECEIVE_PORT);
    
    //@ PACK_PROOF_OBLIGATIONS(dummy)
    struct item *m = network_receive(net_stat);
    check_is_data(m);
    //@ leak proof_obligations(dummy_pub);
    
    network_disconnect(net_stat);
    return m;
}

