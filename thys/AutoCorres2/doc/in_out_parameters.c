/*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#define INT_MAX 2147483647
#define INT_MIN (-2147483647 - 1)

unsigned * global_array;

typedef struct pair {
 unsigned first;
 unsigned second;
} pair_t;

typedef struct int_pair {
 int int_first;
 int int_second;
} int_pair_t;

typedef struct array {
  unsigned elements[3];
} array_t;

typedef struct int_array {
  int int_elements[3];
} int_array_t;

typedef struct pair_array {
  pair_t elements[3];
} pair_array_t;

void inc (unsigned* y) {
  *y = *y + 1;
}

void inc2 (unsigned * y, unsigned * z) {
  inc(y);
  inc(z);
}

void heap_inc2(unsigned * y, unsigned * z) {
  inc2(y, z);
}

void heap_inc2_part(unsigned * y, unsigned * z) {
  inc2(y, z);
}

void heap_inc2_part_swap(unsigned * y, unsigned * z) {
  inc2(y, z);
}

unsigned inc_value (unsigned y) {
  return y + 1;
}

unsigned call_inc_value (unsigned k) {
  unsigned n = 0;
  n = inc_value(k);
  n = n + 1;
  return n;
}

void compare (unsigned * cmp, unsigned i, unsigned j) {
  unsigned result = 0;
  if (i < j) {
    result = 1;
  } else if (j < i) {
    result = 2;
  }
  *cmp = result;
}

unsigned call_compare (unsigned m, unsigned n) {
  unsigned cmp;
  compare(&cmp, m, n);
  return cmp;
}

void call_compare_ptr (unsigned *m, unsigned i, unsigned j) {
  unsigned cmp = 0;
  compare(&cmp, i, j);
  *m = i; 
}



void inc_int (int* y) {
  if (*y == INT_MAX) { 
    exit(1);
  } else {
    *y = *y + 1;
  }
}

void inc_int2 (int * y, int * z) {
  inc_int(y);
  inc_int(z);
}

int call_inc_int (int i) {
  inc_int(&i);
  return i;
}

void inc_int_no_exit(int * y) {
  *y = *y + 1;
}

void mixed_cond_exit(int y) {
  if (y > 0) {
    inc_int_no_exit(&y);
  } else {
    inc_int(&y);
  }
}

void always_exit(unsigned y) {
  inc(&y);
  exit(1);
}

unsigned always_return(unsigned y) {
  inc(&y);
  return y;
}

unsigned always_return1(unsigned y) {
  unsigned z = 0;
  inc(&z);
  return z;
}

void call_inc_int_other (int n, int * m) {
  inc_int(&n);
  *m = n;
}

void call_inc_int_other_mixed (int n, int * m) {
  inc_int(&n);
  inc_int_no_exit(&n);
  *m = n;
}

void call_inc_int_ptr (int * i) {
  inc_int(i);
}

void call_inc_int2 (int * n, int m) {
  inc_int2 (&m, n);
}

void call_inc_int_pair (int_pair_t * p) {
  inc_int2 (&(p->int_first), &(p->int_second));
}

void call_inc_int_array (int_array_t * p, unsigned i) {
  inc_int(&(p->int_elements[i]));
}

/*
void call_inc_int_ptr_first (int_pair_t * p) {
  inc_int(&(p->int_first));
}
*/

void call_inc_ptr_first (pair_t * p) {
  inc(&(p->first));
}


void call_exit(void) {
  exit(42);
}

unsigned get_arr_idx (array_t* arr, unsigned idx) {
  return (arr->elements[idx]);
} 

unsigned get_pair_arr_idx_second (pair_array_t* arr, unsigned idx) {
  return (arr->elements[idx].second);
} 

void inc_pair(pair_t * p) {
  p->first = p->first + 1;
  p->second = p->second + 1;
}


void inc_ptr_first(pair_t * p) {
  inc(&(p->first));
}


void inc_global_array(unsigned idx) {
  inc(&(global_array[idx]));
}

void inc_global_array2(unsigned i, unsigned j) {
  inc2(&(global_array[i]), &(global_array[j]));
}

void call_inc_global_array(unsigned idx) {
  inc_global_array(idx);
}

pair_t call_inc_pair (pair_t p) {
  inc_pair(&p);
  return p;
}

void dec (unsigned* y) {
  *y = *y - 1;
}

void keep_inc (unsigned* y) {
  *y = *y + 1;
}

void keep_inc2 (unsigned* y, unsigned * z) {
  *y = *y + 1;
  *z = *z +1;
}


void keep_inc_global_array(unsigned idx) {
  keep_inc(&(global_array[idx]));
}

void keep_inc_global_array2(unsigned i, unsigned j) {
  keep_inc2(&(global_array[i]), &(global_array[j]));

}

void call_keep_inc_global_array(unsigned idx) {
  keep_inc_global_array(idx);
}

void mixed_global_local_inc(unsigned i, unsigned j, unsigned * p, unsigned * q) {
  keep_inc(&(global_array[i]));
  inc(p);
  inc(q);
  inc(&(global_array[i]));
  call_keep_inc_global_array(i);
  call_inc_global_array(i);
  keep_inc_global_array2(i, j);
  inc_global_array2(j, i);
  keep_inc2(&(global_array[i]), &(global_array[j]));
  inc2(&(global_array[i]), &(global_array[j]));
  inc(&(global_array[2]));
}

int safe_add(int* result, int a, int b) {
    *result = 0;
    if (a > 0 && b > INT_MAX - a) {
        return 0;
    } else if (a < 0 && b < INT_MIN - a) {
        return 0;
    }
    *result = a + b;
   return 1;
}

int call_safe_add(int x, int y) {
  int z;
  if (safe_add(&z, x, y)) {
    return z;
  }
  else {
    exit(1);
  }
}

int add_exit(int a, int b) {
    if (a > 0 && b > INT_MAX - a) {
        exit(1);
    } else if (a < 0 && b < INT_MIN - a) {
        exit(1);
    }
   return a + b;
}

int call_add_exit (int x, int y) {
  int r = 0;
  r = add_exit(x, y);
  r = r + r;
  return r;
}

int g;
void call_add_exit_global (int x, int y) {
  g = add_exit(x, y);
  g = g + g;
}


pair_t inc_first (pair_t p) {
  inc(&(p.first));
  return p;
}

pair_t inc_both (pair_t p) {
  inc(&(p.first));
  inc(&(p.second));
  return p;
}

array_t inc_element (array_t arr, unsigned i) {
  inc(&(arr.elements[i]));
  return arr;
} 
void inc_twice (unsigned* y, unsigned n) {
  *y = *y + n;
  *y = *y + n;
}

unsigned local_inc(unsigned m) {
  *(&m) = *(&m) + 1;
  return m;
}

unsigned inc_in_out (unsigned n) {
  return (n + 1);
}

unsigned cond_inc (unsigned n, unsigned c) {
  if (c > 0) {
    inc (&n);
  }
  return n;
}

unsigned cond_inc1(unsigned cond, unsigned n, unsigned m, unsigned k) {
  if (cond) {
    inc(&n);
  } else {
    k = inc_value(k);
  }
  return n + m + k;
}

unsigned while_inc (unsigned n, unsigned k, unsigned m) {
  while (m > 0) {
    inc (&n);
    k++;
    m--;
  }
  return n + k;
}

unsigned global_m = 0;
unsigned while_inc_global (unsigned n, unsigned k) {
  while (global_m > 0) {
    inc (&n);
    k++;
    global_m--;
  }
  return n + k;
}

unsigned cond_inc_global (unsigned n) {
  if (global_m > 0) {
    inc (&n);
  }
  return n + global_m;
}


void swap (unsigned *x, unsigned * y) {
  unsigned tmp = *x;
  *x = *y;
  *y = tmp;
}

void swap_pair(pair_t * x, pair_t * y) {
  swap(&(x->first), &(y->first));
}

pair_t swap_pair_fst_snd (pair_t p) {
  swap(&(p.first), &(p.second));
  return p;
}


unsigned call_inc_parameter(unsigned n) {
  inc(&n);
  return(n);
}

unsigned keep_call_inc_parameter(unsigned n) {
  keep_inc(&n);
  return(n);
}

unsigned call_inc_in_out_parameter(unsigned n) {
  n = inc_in_out(n);
  return(n);
}

void call_inc_ptr(unsigned *p) {
  inc(p);
}

void call_inc_in_out_ptr(unsigned *p) {
  *p = inc_in_out(*p);
}

unsigned call_inc_uninitialized (void) {
  unsigned m;
  inc(&m);
  return m;
}

unsigned keep_call_inc_uninitialized (void) {
  unsigned m;
  keep_inc(&m);
  return m;
}

unsigned fac(unsigned n) {
  unsigned m = n;
  if (n == 0) {
    return 1;
  } else {
    dec(&n);
    return m * fac(n); 
  }
}

unsigned odd(unsigned n);
unsigned even(unsigned n) {
  if (n == 0) {
     return 1;
  } else {
     dec(&n);
     return odd(n);
  }
};
unsigned odd(unsigned n) {
  if (n == 1) {
    return 1;
  } else {
    dec(&n);
    return even(n);
  }
};

void xyz(unsigned *x, unsigned n) {
    unsigned p, m;
    int i;

    p = 0;
    *x = 0;
    for(i=0; i<16; i++) {
        m = ((p & (1 << i)) == 0);
        *x |= m << i;
        p = m ? p + (n<<i) : p;
    }
}

unsigned glob;

void inc_glob (unsigned n) {
  inc(&n);
  glob = glob + n;
}

void set_glob (unsigned n) {
  glob = n;
}


void abab(unsigned ab, unsigned a, unsigned b) {
    int          i;
    unsigned      aWord, bWord, abWord;

    for(i=0; i<ab; i++) {
        aWord = i<a ? 1 : 0;
        bWord = i<b ? 1 : 0;
        abWord = aWord & bWord;
    }
}


void kc(unsigned sz, int k) {
    int i;
    unsigned c;

    c = 0;
    for(i=0; i<sz; i++) {
        if (c) {
            if (k) {
                c = 1;
                k = 1;
            }
            else {
                c = 1;
                k = 0;
            }
        }
        else {
            if (k) {
                c = 0;
                k = 1;
            }
            else {
                c = 0;
                k = 0;
            }
        }
    }
}

void resab(unsigned *res, unsigned ab, unsigned b) {
    int i;
    unsigned a;

    *res = 0;
    for(i=0; i<ab; i++) {
      a = ((*res == b) || (*res != 1 && b == 0)) ? 0x0 : 0xFFFFFFFF;
    }
}

void abnestedloop(unsigned ab, unsigned a, unsigned b) {
    int i, j;
    unsigned long long aWord, bWord, t0, t1, abl, abh;

    for(i=0; i<a; i++) {
        aWord = 0;
        for(j=0; j<b; j++) {
            bWord = 0;

            abl = aWord * bWord;
            abh = abl >> 16;
            abl = abl & 0xFFFFFFFF;

            t0 = abl + t1;
            t1 = t0 >> 16;
            t0 = t0 & 0xFFFFFFFF;
            t1 = t1 + abh;
        }
        if(i+j < ab) {
            t1 = t1 + abh;
        }
        t1 = 0;
    }
}

typedef struct twice {
  unsigned size;
  unsigned addr;
} tw;

void out(unsigned *out, tw cmp0, tw cmp1) {
  *out = 1;
}

unsigned out_seq(unsigned *out, unsigned x, unsigned y) {
  inc(&x);
  inc(&y);
  y = x + y;
  *out = x + y;
  return 1;
}

unsigned read(unsigned a) {
  return a+1;
}

void abcmp(unsigned * cmpRst, tw ab, tw a, tw cmp0, tw cmp1, unsigned cond) {
    int          i;
    unsigned      aWord, bWord, abWord;

    out(cmpRst, cmp0, cmp1);
    for(i=0; i<ab.size; i++) {
        aWord = i<a.size ? read(a.addr+i) : 0;
        bWord = ((*cmpRst == cond) || (*cmpRst != 0x1 && cond == 0x2)) ? 0x0 : 0xFFFFFFFF;
        abWord = aWord | bWord;
    }
}

void out2(unsigned *out, unsigned in) {
  *out = *out + in + 1;
}

void out2_read(tw ab, tw a, tw b, tw n) {
    unsigned inout;
    out2(&inout, read(n.addr));
}


unsigned nested_loop(unsigned x, unsigned y) {
  unsigned res;
  res = 0;
  for (unsigned i = 0; i <= x; i++) {
    for (unsigned j = i; j <= y; j++) {
       inc(&res); 
    }
    return res;
  }
}

void finally_elimination1(unsigned x) {
  if (x > 2) {
     inc(&x);
     return;
  };
 inc(&x);
}

void finally_elimination2(unsigned x) {
  if (x > 2) {
     x = inc_value(x);
     return;
  };
  inc(&x);
}

unsigned nested_loop1(unsigned x, unsigned y) {
  unsigned res = 0;
  unsigned i = 0;
  unsigned j = 0;
  while (i <= x) {
    j = i;
    while (j <= y) {
       inc(&res);
       inc(&j); 
    }

    inc(&i);
  }
  return res;
}

unsigned nested_loop2(unsigned x, unsigned y) {
  unsigned res = 0;
  unsigned i = 0;
  unsigned j = 0;
  while (i <= x) {
    j = i;
    while (j <= y) {
       res = res + 1;
       j = j + 1; 
    }

    i = i + 1;
  }
}

void inc_another(unsigned *x, unsigned y) {
  inc(&y);
  *x = *x + y;
}


void inc_loop (unsigned * x, unsigned * y) {
  while (*x != *y) {
    inc(y);
  }
}



unsigned loop_tuple_prj (unsigned n) {
  pair_t p;
  unsigned i = 0;
  unsigned result = 0;
  while (i <= n) {
   i = i + 1;
   p.first = i;
   p.second = i;
   inc_pair(&p);
   result = result + p.first + p.second;
  } 
  return result;
}

void keep_modify (unsigned * p, unsigned * q) {
  *p = *q;
  *q = 42;
}

unsigned keep_unmodified (unsigned * p, unsigned * q) {
 return (*p) + (*q);
}

unsigned shuffle(unsigned char *buf, unsigned char len){
 unsigned tmp= 0;
 if (len > 4){
  return 42;
 }
 for(int i = 0; i < len; i++){
  tmp |= (unsigned)(*(buf - i)) << (i*8);
 }
 return tmp;
}


void global_array_update(unsigned idx, unsigned v){
    global_array[idx*4] = v;
    global_array[(idx*4)+1] = v+1;
}

unsigned int state = 0;

/** DONT_TRANSLATE
    FNSPEC step_spec: "\<forall>st. \<Gamma> \<turnstile> \<lbrace>\<acute>state = st \<rbrace> Call step_'proc \<lbrace>abs_step st \<acute>state\<rbrace>" 
    MODIFIES: state
*/
void step(void);

unsigned char f(unsigned char x) {
  return x + 1;
}

void assert_0(unsigned char c) {
  if (c == 0) exit(-1);
}

unsigned char g1(unsigned char *out)
{
	unsigned char x = *out;
	for (unsigned char i = 0; i <= 1; i++) {
		if (i == 0) {
			x = f(x);
			if (x != 0) {
				*out = x;
			}
			break;
		}
		assert_0(x);
	}
	return x;
}

void *state_ptr;

void set_void(void *p) {
  state_ptr = p;
}

void set_void2(void *p) {
  set_void(p);
}

void set_byte(unsigned char *p) {
  set_void((void *)p);
}

int_pair_t cast_pair(pair_t p) {
	return *((int_pair_t*)&p);
}

unsigned char read_char (unsigned char **p, long unsigned int *len)
{
        unsigned char tmp = **p;
        (*len)--;
        (*p)++;
        return tmp;
}

unsigned char call_read_char (unsigned char *p, long unsigned int len) {
  if (*p == 0) {exit(1);}
  unsigned char res = read_char(&p, &len);
  return res;
}

unsigned char call_read_char_loop (unsigned char *p, long unsigned int len) {
  unsigned char res = 0;
  while (*p != 0) {
    res = read_char(&p, &len);
  }
  return res;
}

unsigned goto_read_char1 (pair_t * p) {
  unsigned status = 0;
  unsigned char res1 = 0;
  unsigned char len1 = 0;
  const unsigned char *q = 0;
  long unsigned int len = 0;
  long long unsigned int flags = 0;
  res1 = read_char(&q, &len);
  flags = res1 & 0xEE;
    if ( flags == 0xEE ) {
        do { if (__builtin_expect(!( *q != 0x71), 0)) goto exit; } while (0);
    }
  p->first = 1;
  len1 = read_char(&q, &len);
  status = 1;
exit:
  return status; 
}


unsigned goto_read_char3 (pair_t * p) {
  unsigned status = 0;
  unsigned char res1 = 0;
  unsigned char len1 = 0;
  const unsigned char *q = 0;
  long unsigned int len = 0;
  long long unsigned int flags = 0;
  res1 = read_char(&q, &len);
  flags = res1 & 0xEE;
    if ( flags == 0xEE ) {
        do { if (__builtin_expect(!( *q != 0x71), 0)) goto exit; } while (0);
    }
  p->first = 1;
/*  len1 = read_char(&q, &len);*/
  status = 1;
exit:
  return status; 
}

unsigned goto_read_char4 (pair_t * p) {
  unsigned status = 0;
  unsigned char res1 = 0;
  unsigned char len1 = 0;
  const unsigned char *q = 0;
  long unsigned int len = 0;
  long long unsigned int flags = 0;
	do { if (__builtin_expect(!(p), 0)) goto exit; } while (0);
  res1 = read_char(&q, &len);
  flags = res1 & 0xEE;
    if ( flags == 0xEE ) {
        do { if (__builtin_expect(!( *q != 0x71), 0)) goto exit; } while (0);
    }
  p->first = 1;
  len1 = read_char(&q, &len);
  status = 1;
exit:
  return status; 
}

typedef struct elem {
 unsigned first;
 unsigned char * content;
} elem_t;

elem_t *  glob_elem;

unsigned goto_read_char2 (elem_t * p, unsigned char *d) {
  unsigned status = 0;
	const unsigned char *q = 0;
	long unsigned int len = 0;
	unsigned char res1 = 0;
	do { if (__builtin_expect(!(p), 0)) goto exit; } while (0);
	do { if (__builtin_expect(!(p->first), 0)) goto exit; } while (0);
	if (__builtin_expect(!(d), 0)) goto exit;
  len = p->first;
  q = glob_elem->content;
  res1 = read_char (&q, &len);
  status = 1;
exit:
  return status;
  
}

unsigned goto_read_char5(elem_t        *elem, long unsigned int cmp)
{
    unsigned return_status = 0;

    if (elem->first != 4)
    {
       return_status = 0;
       goto exit;
    }

    unsigned char a0 = elem->content[0];
    unsigned char a1 = elem->content[1];
    unsigned char a2 = elem->content[2];
    unsigned char a3 = elem->content[3];

    unsigned char b0 = (cmp & 0xFF0F00F0) >> 24;

    if (a0 != b0)
    {
      return_status = 0;
      goto exit;
    }
    return_status = 1;

exit:
    return return_status;
}
