#ifndef JC_RINGBUF_H
#define JC_RINGBUF_H

#include "jc_types.h"

typedef struct {
  jc_u8 *data;
  jc_u16 size;
  jc_u16 head;
  jc_u16 tail;
} jc_ringbuf;

void jc_ringbuf_init(jc_ringbuf *rb, jc_u8 *storage, jc_u16 size);
int jc_ringbuf_is_empty(const jc_ringbuf *rb);
int jc_ringbuf_is_full(const jc_ringbuf *rb);
jc_u16 jc_ringbuf_count(const jc_ringbuf *rb);
int jc_ringbuf_push(jc_ringbuf *rb, jc_u8 value);
int jc_ringbuf_pop(jc_ringbuf *rb, jc_u8 *out);

#endif /* JC_RINGBUF_H */
