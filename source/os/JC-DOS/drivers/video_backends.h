#ifndef JC_VIDEO_BACKENDS_H
#define JC_VIDEO_BACKENDS_H

#include "jc_contracts.h"
#include "jc_display.h"
#include "jc_error.h"

jc_error_t jc_video_mc6845_probe(const jc_bdt_header_v1 *bdt,
                                 jc_display_backend *out);
jc_error_t jc_video_mda_probe(const jc_bdt_header_v1 *bdt,
                              jc_display_backend *out);
jc_error_t jc_video_cga_ega_vga_probe(const jc_bdt_header_v1 *bdt,
                                      jc_display_backend *out);
jc_error_t jc_video_tms9918_probe(const jc_bdt_header_v1 *bdt,
                                  jc_display_backend *out);
jc_error_t jc_video_v99x8_probe(const jc_bdt_header_v1 *bdt,
                                jc_display_backend *out);

#endif /* JC_VIDEO_BACKENDS_H */
