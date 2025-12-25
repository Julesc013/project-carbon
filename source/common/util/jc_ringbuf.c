#include "jc_ringbuf.h"

void jc_ringbuf_init(jc_ringbuf *rb, jc_u8 *storage, jc_u16 size) {
  if (!rb) {
    return;
  }
  rb->data = storage;
  rb->size = size;
  rb->head = 0;
  rb->tail = 0;
}

int jc_ringbuf_is_empty(const jc_ringbuf *rb) {
  if (!rb) {
    return 1;
  }
  return rb->head == rb->tail;
}

int jc_ringbuf_is_full(const jc_ringbuf *rb) {
  jc_u16 next;
  if (!rb || rb->size == 0) {
    return 1;
  }
  next = (jc_u16)((rb->head + 1u) % rb->size);
  return next == rb->tail;
}

jc_u16 jc_ringbuf_count(const jc_ringbuf *rb) {
  if (!rb || rb->size == 0) {
    return 0;
  }
  if (rb->head >= rb->tail) {
    return (jc_u16)(rb->head - rb->tail);
  }
  return (jc_u16)(rb->size - (rb->tail - rb->head));
}

int jc_ringbuf_push(jc_ringbuf *rb, jc_u8 value) {
  jc_u16 next;
  if (!rb || rb->size == 0) {
    return 0;
  }
  next = (jc_u16)((rb->head + 1u) % rb->size);
  if (next == rb->tail) {
    return 0;
  }
  rb->data[rb->head] = value;
  rb->head = next;
  return 1;
}

int jc_ringbuf_pop(jc_ringbuf *rb, jc_u8 *out) {
  if (!rb || !out || rb->size == 0) {
    return 0;
  }
  if (rb->head == rb->tail) {
    return 0;
  }
  *out = rb->data[rb->tail];
  rb->tail = (jc_u16)((rb->tail + 1u) % rb->size);
  return 1;
}
