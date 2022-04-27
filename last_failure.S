# last failing test case:
#>QCVENGINE_TEST_V2.0
.4byte 0x00090913 # addi x18, x18, 0
.4byte 0x00100613 # addi x12, x0, 1
.4byte 0x01f61613 # slli x12, x12, 31
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x02067227 # vstore v4, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x02067127 # vstore v2, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x020679a7 # vstore v19, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00090913 # addi x18, x18, 0
.4byte 0x022209d7 # vadd_vv v19, v4, v2
.4byte 0x020679a7 # vstore v19, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00863683 # ld x13, x12[8]
.4byte 0x00088893 # addi x17, x17, 0
.4byte 0x00100613 # addi x12, x0, 1
.4byte 0x01f61613 # slli x12, x12, 31
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x020678a7 # vstore v17, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x02067a27 # vstore v20, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x020678a7 # vstore v17, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00088893 # addi x17, x17, 0
.4byte 0x0348c8d7 # vadd_vx v17, x17, v20
.4byte 0x020678a7 # vstore v17, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00863683 # ld x13, x12[8]
.4byte 0x00020213 # addi x4, x4, 0
.4byte 0x00100613 # addi x12, x0, 1
.4byte 0x01f61613 # slli x12, x12, 31
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x02067127 # vstore v2, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x020678a7 # vstore v17, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x02067827 # vstore v16, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00020213 # addi x4, x4, 0
.4byte 0x03110857 # vadd_vv v16, v2, v17
.4byte 0x02067827 # vstore v16, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00863683 # ld x13, x12[8]
.4byte 0x00098993 # addi x19, x19, 0
.4byte 0x00100613 # addi x12, x0, 1
.4byte 0x01f61613 # slli x12, x12, 31
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x020678a7 # vstore v17, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x02067827 # vstore v16, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x020678a7 # vstore v17, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00098993 # addi x19, x19, 0
.4byte 0x030888d7 # vadd_vv v17, v17, v16
.4byte 0x020678a7 # vstore v17, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00863683 # ld x13, x12[8]
.4byte 0x00100613 # addi x12, x0, 1
.4byte 0x01f61613 # slli x12, x12, 31
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x02067027 # vstore v0, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00863683 # ld x13, x12[8]
#>START_NO_SHRINK
.4byte 0x00b00613 # addi x12, x0, 11
.4byte 0x01761613 # slli x12, x12, 23
.4byte 0x30062073 # csrrs x0, mstatus (0x300), x12
.4byte 0x00400713 # addi x14, x0, 4
.4byte 0x00477657 # vsetvli x12, x14, vsew: 1
.4byte 0x00100613 # addi x12, x0, 1
.4byte 0x01f61613 # slli x12, x12, 31
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x00000693 # addi x13, x0, 0
.4byte 0x00d63023 # sd x13, x12[0]
.4byte 0x02067007 # vload v0, x12
.4byte 0x02067087 # vload v1, x12
.4byte 0x02067107 # vload v2, x12
.4byte 0x02067187 # vload v3, x12
.4byte 0x02067207 # vload v4, x12
.4byte 0x02067287 # vload v5, x12
.4byte 0x02067307 # vload v6, x12
.4byte 0x02067387 # vload v7, x12
.4byte 0x02067407 # vload v8, x12
.4byte 0x02067487 # vload v9, x12
.4byte 0x02067507 # vload v10, x12
.4byte 0x02067587 # vload v11, x12
.4byte 0x02067607 # vload v12, x12
.4byte 0x02067687 # vload v13, x12
.4byte 0x02067707 # vload v14, x12
.4byte 0x02067787 # vload v15, x12
.4byte 0x02067807 # vload v16, x12
.4byte 0x02067887 # vload v17, x12
.4byte 0x02067907 # vload v18, x12
.4byte 0x02067987 # vload v19, x12
.4byte 0x02067a07 # vload v20, x12
.4byte 0x02067a87 # vload v21, x12
.4byte 0x02067b07 # vload v22, x12
.4byte 0x02067b87 # vload v23, x12
.4byte 0x02067c07 # vload v24, x12
.4byte 0x02067c87 # vload v25, x12
.4byte 0x02067d07 # vload v26, x12
.4byte 0x02067d87 # vload v27, x12
.4byte 0x02067e07 # vload v28, x12
.4byte 0x02067e87 # vload v29, x12
.4byte 0x02067f07 # vload v30, x12
.4byte 0x02067f87 # vload v31, x12
#>END_NO_SHRINK
.4byte 0x00100613 # addi x12, x0, 1
.4byte 0x01f61613 # slli x12, x12, 31
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x57700993 # addi x19, x0, 1399
.4byte 0x01799993 # slli x19, x19, 23
.4byte 0x01363023 # sd x19, x12[0]
.4byte 0x02067187 # vload v3, x12
.4byte 0x00020213 # addi x4, x4, 0
.4byte 0x00100613 # addi x12, x0, 1
.4byte 0x01f61613 # slli x12, x12, 31
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x020671a7 # vstore v3, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x020678a7 # vstore v17, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x02067227 # vstore v4, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00020213 # addi x4, x4, 0
.4byte 0x97126257 # vmul_vx v4, x4, v17
.4byte 0x02067227 # vstore v4, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00863683 # ld x13, x12[8]
.4byte 0x00008093 # addi x1, x1, 0
.4byte 0x00100613 # addi x12, x0, 1
.4byte 0x01f61613 # slli x12, x12, 31
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x02067127 # vstore v2, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x02067027 # vstore v0, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x02067827 # vstore v16, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00008093 # addi x1, x1, 0
.4byte 0x0200c857 # vadd_vx v16, x1, v0
.4byte 0x02067827 # vstore v16, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00863683 # ld x13, x12[8]
.4byte 0x00018193 # addi x3, x3, 0
.4byte 0x00100613 # addi x12, x0, 1
.4byte 0x01f61613 # slli x12, x12, 31
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x02067227 # vstore v4, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x020678a7 # vstore v17, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x02067a27 # vstore v20, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00018193 # addi x3, x3, 0
.4byte 0x83120a57 # vsaddu_vv v20, v4, v17
.4byte 0x02067a27 # vstore v20, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00863683 # ld x13, x12[8]
.4byte 0x00010113 # addi x2, x2, 0
.4byte 0x00100613 # addi x12, x0, 1
.4byte 0x01f61613 # slli x12, x12, 31
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x020670a7 # vstore v1, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x020670a7 # vstore v1, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x02067227 # vstore v4, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00010113 # addi x2, x2, 0
.4byte 0x82108257 # vsaddu_vv v4, v1, v1
.4byte 0x02067227 # vstore v4, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00863683 # ld x13, x12[8]
.4byte 0x00100613 # addi x12, x0, 1
.4byte 0x01f61613 # slli x12, x12, 31
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0xe8d00193 # addi x3, x0, -371
.4byte 0x00519193 # slli x3, x3, 5
.4byte 0x00363023 # sd x3, x12[0]
.4byte 0x02067907 # vload v18, x12
.4byte 0x00008093 # addi x1, x1, 0
.4byte 0x00100613 # addi x12, x0, 1
.4byte 0x01f61613 # slli x12, x12, 31
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x02067927 # vstore v18, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x02067827 # vstore v16, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x020679a7 # vstore v19, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00008093 # addi x1, x1, 0
.4byte 0x8b00c9d7 # vssubu_vx v19, x1, v16
.4byte 0x020679a7 # vstore v19, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00863683 # ld x13, x12[8]
.4byte 0x00098993 # addi x19, x19, 0
.4byte 0x00100613 # addi x12, x0, 1
.4byte 0x01f61613 # slli x12, x12, 31
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x020671a7 # vstore v3, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x020671a7 # vstore v3, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x020670a7 # vstore v1, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00098993 # addi x19, x19, 0
.4byte 0x0a39c0d7 # vsub_vx v1, x19, v3
.4byte 0x020670a7 # vstore v1, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00863683 # ld x13, x12[8]
.4byte 0x00098993 # addi x19, x19, 0
.4byte 0x00100613 # addi x12, x0, 1
.4byte 0x01f61613 # slli x12, x12, 31
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x02067227 # vstore v4, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x02067127 # vstore v2, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x02067a27 # vstore v20, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00098993 # addi x19, x19, 0
.4byte 0x0a29ca57 # vsub_vx v20, x19, v2
.4byte 0x02067a27 # vstore v20, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00863683 # ld x13, x12[8]
.4byte 0x00018193 # addi x3, x3, 0
.4byte 0x00100613 # addi x12, x0, 1
.4byte 0x01f61613 # slli x12, x12, 31
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x02067927 # vstore v18, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x020671a7 # vstore v3, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x020671a7 # vstore v3, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00018193 # addi x3, x3, 0
.4byte 0x823901d7 # vsaddu_vv v3, v18, v3
.4byte 0x020671a7 # vstore v3, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00863683 # ld x13, x12[8]
.4byte 0x00090913 # addi x18, x18, 0
.4byte 0x00100613 # addi x12, x0, 1
.4byte 0x01f61613 # slli x12, x12, 31
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x02067a27 # vstore v20, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x020670a7 # vstore v1, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x020678a7 # vstore v17, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00090913 # addi x18, x18, 0
.4byte 0x821c38d7 # vsaddu_vi v17, v1, 24
.4byte 0x020678a7 # vstore v17, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00863683 # ld x13, x12[8]
.4byte 0x00000013 # addi x0, x0, 0
.4byte 0x00100613 # addi x12, x0, 1
.4byte 0x01f61613 # slli x12, x12, 31
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x02067227 # vstore v4, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x02067227 # vstore v4, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x02067227 # vstore v4, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00000013 # addi x0, x0, 0
.4byte 0x0a420257 # vsub_vv v4, v4, v4
.4byte 0x02067227 # vstore v4, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00863683 # ld x13, x12[8]
.4byte 0x00080813 # addi x16, x16, 0
.4byte 0x00100613 # addi x12, x0, 1
.4byte 0x01f61613 # slli x12, x12, 31
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x02067127 # vstore v2, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x02067827 # vstore v16, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x02067a27 # vstore v20, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00080813 # addi x16, x16, 0
.4byte 0x0b084a57 # vsub_vx v20, x16, v16
.4byte 0x02067a27 # vstore v20, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00863683 # ld x13, x12[8]
.4byte 0x00000013 # addi x0, x0, 0
.4byte 0x00100613 # addi x12, x0, 1
.4byte 0x01f61613 # slli x12, x12, 31
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x00460613 # addi x12, x12, 4
.4byte 0x02067a27 # vstore v20, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x02067027 # vstore v0, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x020671a7 # vstore v3, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00000013 # addi x0, x0, 0
.4byte 0x820041d7 # vsaddu_vx v3, x0, v0
.4byte 0x020671a7 # vstore v3, x12
.4byte 0x00063683 # ld x13, x12[0]
.4byte 0x00863683 # ld x13, x12[8]
# Test end