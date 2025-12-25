#ifndef JC_ASSERT_H
#define JC_ASSERT_H

#define JC_STATIC_ASSERT(name, expr) typedef char jc_static_assert_##name[(expr) ? 1 : -1]

#define JC_OFFSETOF(type, member) \
  ((unsigned long)((char *)&(((type *)0)->member) - (char *)((type *)0)))

#define JC_ALIGNOF(type) \
  ((unsigned long)(&(((struct { char c; type t; } *)0)->t)))

#endif /* JC_ASSERT_H */
