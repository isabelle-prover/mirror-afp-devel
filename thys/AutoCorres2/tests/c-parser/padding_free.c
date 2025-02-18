typedef unsigned char  uint8_t;
typedef unsigned short uint16_t;
typedef unsigned int   uint32_t;

typedef struct {
  uint8_t field1;
  uint8_t pad1;
  uint16_t field2;
  uint16_t pad2;
  uint8_t field3;
  uint8_t field4;
  uint32_t pad3;
} p_t;

typedef struct {
  uint16_t field1;
  uint16_t pad1;
  uint32_t field2;
} q_t;

typedef struct {
  uint32_t field1;
  uint16_t pad1;
  uint16_t field2;
} r_t;

uint8_t f(p_t p) {
  return p.field1;
}

uint16_t g(q_t q) {
  return q.field1;
}

uint32_t h(r_t r) {
  return r.field1;
}