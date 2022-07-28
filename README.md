# Glibc FSOP code path finder

Find FSOP code path that can hijack control flow and stack pointer in GLIBC Libio.

## Description:

1. Install this plugin
2. Open `libc.so.6` in Binary ninja, then click `Tools -> Plugins -> Find FSOP code path`
3. You should see the result in `Log` windows

## Useful discoveries:

```
// GLIBC 2.34-0ubuntu3.2
 3. _IO_wfile_underflow_mmap@0x86030 -> _IO_wdoallocbuf@0x83be0
    0x8614d: call(0x83be0)
      RIP/RDI DATAFLOW:
       rbx = rdi -> rdi = rbx -> call(0x83be0)
      RBP DATAFLOW:
       rbp = [rdi + 0x98].q
      CODE PATH:
       eax = [rdi].d
        => [condition] (al & 4) == 0
       rax = [rdi + 0xa0].q
       rdx = [rax].q
        => [condition] rdx u>= [rax + 8].q
       rdx = [rdi + 8].q
        => [condition] rdx u< [rdi + 0x10].q
       rdi = [rax + 0x40].q
        => [condition] rdi == 0
    0x83c0b: call([rax + 0x68].q)
      RIP/RDI DATAFLOW:
       rax = [rdi + 0xa0].q -> rax = [rax + 0xe0].q -> call([rax + 0x68].q)
      RBP DATAFLOW:
       (N/A)
      CODE PATH:
       rax = [rdi + 0xa0].q
        => [condition] [rax + 0x30].q == 0
        => [condition] ([rdi].b & 2) == 0
  ([0x216020] is the location of _IO_wfile_underflow_mmap in __libc_IO_vtables)
```

A FSOP code path which can be used to **perform stack migration** with a single FSOP attack, available on GLIBC 2.24+. It's also known as [house of apple2](https://bbs.pediy.com/thread-273832.htm) independently found by [roderick01](https://roderickchan.github.io/). 

I actually found this code path *few weeks ago* but was struggling to work on other stuffs these day, so I didn't notice someone has published this code path already X(

## License

This plugin is released under an [MIT license](./LICENSE).