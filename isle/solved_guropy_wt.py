unsolved = []
solved_gurobi =[
"metro_9_9_10_35_13_7_500_2_6.lp.sm-extracted.wcnf.gz",
"metro_9_8_7_22_10_6_500_1_2.lp.sm-extracted.wcnf.gz",
"metro_9_8_7_30_10_6_500_1_6.lp.sm-extracted.wcnf.gz",
"metro_9_9_10_35_13_7_500_2_4.lp.sm-extracted.wcnf.gz",
"metro_9_8_7_22_10_6_500_1_1.lp.sm-extracted.wcnf.gz",
"inst22.lp.sm-extracted.wcnf.gz",
"metro_8_8_5_20_10_6_500_1_0.lp.sm-extracted.wcnf.gz",
"metro_9_9_10_35_13_7_500_2_2.lp.sm-extracted.wcnf.gz",
"metro_9_8_7_22_10_6_500_1_9.lp.sm-extracted.wcnf.gz",
"mancoosi-test-i40d0u98-10.wcnf.gz",
"mancoosi-test-i30d0u98-8.wcnf.gz",
"mancoosi-test-i20d0u98-5.wcnf.gz",
"mancoosi-test-i20d0u98-15.wcnf.gz",
"mancoosi-test-i40d0u98-14.wcnf.gz",
"mancoosi-test-i3000d0u98-51.wcnf.gz",
"mancoosi-test-i3000d0u98-56.wcnf.gz",
"mancoosi-test-i1000d0u98-11.wcnf.gz",
"mancoosi-test-i1000d0u98-24.wcnf.gz",
"mancoosi-test-i3000d0u98-68.wcnf.gz",
"rand446_l1.wcnf.gz",
"rand869_l1.wcnf.gz",
"cap71.wcsp.wcnf.gz",
"cap91.wcsp.wcnf.gz",
"cap132.wcsp.wcnf.gz",
"cap92.wcsp.wcnf.gz",
"cap131.wcsp.wcnf.gz",
"warehouse0.wcsp.wcnf.gz",
"warehouse1.wcsp.wcnf.gz",
"cap72.wcsp.wcnf.gz",
"muni-fi-fal17.wcnf.gz",
"agh-ggos-spr17.wcnf.gz",
"agh-h-spr17.wcnf.gz",
"muni-fi-spr17.wcnf.gz",
"nbi-spr18.wcnf.gz",
"muni-fi-spr16.wcnf.gz",
"muni-fsps-spr17c.wcnf.gz",
"muni-fsps-spr17.wcnf.gz",
"agh-fis-spr17.wcnf.gz",
"tg-fal17.wcnf.gz",
"muni-fspsx-fal17.wcnf.gz",
"tg-spr18.wcnf.gz",
"normalized-factor-size=9-P=331-Q=331.opb.wcnf.gz",
"normalized-factor-size=9-P=23-Q=379.opb.wcnf.gz",
"normalized-factor-size=9-P=89-Q=487.opb.wcnf.gz",
"normalized-factor-size=9-P=127-Q=211.opb.wcnf.gz",
"normalized-factor-size=9-P=127-Q=359.opb.wcnf.gz",
"normalized-factor-size=9-P=107-Q=373.opb.wcnf.gz",
"normalized-factor-size=9-P=263-Q=367.opb.wcnf.gz",
"normalized-factor-size=9-P=307-Q=449.opb.wcnf.gz",
"normalized-factor-size=9-P=149-Q=509.opb.wcnf.gz",
"normalized-factor-size=9-P=157-Q=163.opb.wcnf.gz",
"normalized-factor-size=9-P=157-Q=373.opb.wcnf.gz",
"normalized-factor-size=9-P=191-Q=509.opb.wcnf.gz",
"power-distribution_10_2.wcnf.gz",
"power-distribution_11_3.wcnf.gz",
"power-distribution_9_2.wcnf.gz",
"power-distribution_6_2.wcnf.gz",
"power-distribution_8_2.wcnf.gz",
"power-distribution_6_3.wcnf.gz",
"power-distribution_6_6.wcnf.gz",
"ped2.B.recomb1-0.10-9.wcnf.gz",
"ped3.G.recomb10-0.10-8.wcnf.gz",
"ped2.B.recomb1-0.10-10.wcnf.gz",
"ped3.F.recomb10-0.01-2.wcnf.gz",
"ped2.G.recomb5-0.01-4.wcnf.gz",
"ped2.B.recomb1-0.10-6.wcnf.gz",
"ram_k3_n9.ra1.wcnf.gz",
"ram_k4_n19.ra1.wcnf.gz",
"ram_k3_n20.ra1.wcnf.gz",
"ram_k3_n15.ra1.wcnf.gz",
"ram_k4_n20.ra1.wcnf.gz",
"ram_k3_n11.ra1.wcnf.gz",
"ram_k3_n19.ra1.wcnf.gz",
"ram_k3_n13.ra1.wcnf.gz",
"ram_k3_n18.ra1.wcnf.gz",
"ram_k3_n12.ra1.wcnf.gz",
"ram_k3_n10.ra1.wcnf.gz",
"ram_k3_n16.ra1.wcnf.gz",
"role_smallcomp_0.25_9.wcnf.gz",
"role_smallcomp_0.1_1.wcnf.gz",
"role_smallcomp_0.85_6.wcnf.gz",
"role_smallcomp_0.55_2.wcnf.gz",
"limits-10-10_data-1_inst-081_60m.sm-extracted.wcnf.gz",
"limits-10-10_data-1_inst-112_60m.sm-extracted.wcnf.gz",
"limits-10-10_data-1_inst-068_30m.sm-extracted.wcnf.gz",
"limits-10-10_data-1_inst-099_60m.sm-extracted.wcnf.gz",
"limits-10-10_data-1_inst-005_60m.sm-extracted.wcnf.gz",
"limits-10-10_data-1_inst-078_60m.sm-extracted.wcnf.gz",
"frb15-9-3.wcnf.gz",
"frb10-6-2.wcnf.gz",
"frb10-6-4.wcnf.gz",
"frb25-13-1.wcnf.gz",
"frb20-11-1.wcnf.gz",
"frb10-6-5.wcnf.gz",
"frb20-11-4.wcnf.gz",
"frb10-6-3.wcnf.gz",
"frb15-9-2.wcnf.gz",
"frb25-13-4.wcnf.gz",
"frb20-11-2.wcnf.gz",
"frb20-11-3.wcnf.gz",
"drmx-am32-outof-70-esortn-w.wcnf.gz",
"drmx-am20-outof-50-esortn-w.wcnf.gz",
"drmx-am16-outof-45-etot-w.wcnf.gz",
"drmx-am20-outof-50-ecardn-w.wcnf.gz",
"drmx-am28-outof-60-ekmtot-w.wcnf.gz",
"drmx-am32-outof-70-etot-w.wcnf.gz",
"drmx-am12-outof-40-ekmtot-w.wcnf.gz",
"drmx-am24-outof-55-ekmtot-w.wcnf.gz",
"drmx-am20-outof-50-etot-w.wcnf.gz",
"drmx-am12-outof-40-eseqc-w.wcnf.gz",
"drmx-am28-outof-60-esortn-w.wcnf.gz",
"drmx-am32-outof-70-eseqc-w.wcnf.gz",
"WCNF_storage_p07.wcnf.gz",
"WCNF_pathways_p04.wcnf.gz",
"WCNF_pathways_p01.wcnf.gz",
"WCNF_pathways_p07.wcnf.gz",
"WCNF_pathways_p02.wcnf.gz",
"WCNF_pathways_p20.wcnf.gz",
"WCNF_storage_p01.wcnf.gz",
"WCNF_pathways_p08.wcnf.gz",
"WCNF_storage_p06.wcnf.gz",
"WCNF_pathways_p17.wcnf.gz",
"WCNF_pathways_p09.wcnf.gz",
"WCNF_pathways_p11.wcnf.gz",
"p1.wcnf.t.wcnf.gz",
"1vii_.1cph_.g.wcnf.t.wcnf.gz",
"3ebx_.6ebx_.g.wcnf.t.wcnf.gz",
"1knt_.5pti_.g.wcnf.t.wcnf.gz",
"2knt_.5pti_.g.wcnf.t.wcnf.gz",
"1knt_.2knt_.g.wcnf.t.wcnf.gz",
"1knt_.1bpi_.g.wcnf.t.wcnf.gz",
"3ebx_.1era_.g.wcnf.t.wcnf.gz",
"6ebx_.1era_.g.wcnf.t.wcnf.gz",
"1bpi_.2knt_.g.wcnf.t.wcnf.gz",
"1bpi_.5pti_.g.wcnf.t.wcnf.gz",
"sandiaprotein.g.wcnf.t.wcnf.gz",
"cat_reg_60_110_0001.txt.wcnf.gz",
"cat_reg_60_200_0000.txt.wcnf.gz",
"cat_reg_60_110_0000.txt.wcnf.gz",
"cat_paths_60_90_0004.txt.wcnf.gz",
"cat_paths_60_140_0004.txt.wcnf.gz",
"cat_paths_60_160_0002.txt.wcnf.gz",
"cat_paths_60_170_0001.txt.wcnf.gz",
"cat_sched_60_150_0001.txt.wcnf.gz",
"cat_sched_60_200_0004.txt.wcnf.gz",
"cat_sched_60_80_0000.txt.wcnf.gz",
"cat_sched_60_70_0002.txt.wcnf.gz",
"cat_sched_60_200_0002.txt.wcnf.gz",
"test10--n-5000.wcnf.gz",
"test15--n-5000.wcnf.gz",
"test73--n-20000.wcnf.gz",
"test35--n-10000.wcnf.gz",
"test61--n-20000.wcnf.gz",
"test69--n-20000.wcnf.gz",
"test42--n-15000.wcnf.gz",
"test57--n-15000.wcnf.gz",
"test2--n-5000.wcnf.gz",
"test27--n-10000.wcnf.gz",
"test59--n-15000.wcnf.gz",
"test33--n-10000.wcnf.gz",
"causal_n6_i8_N1000_uai14_log_int.wcnf.gz",
"tcp_students_112_it_15.wcnf.gz",
"tcp_students_91_it_5.wcnf.gz",
"tcp_students_112_it_12.wcnf.gz",
"tcp_students_91_it_8.wcnf.gz",
"tcp_students_91_it_15.wcnf.gz",
"tcp_students_105_it_14.wcnf.gz",
"tcp_students_112_it_4.wcnf.gz",
"tcp_students_91_it_1.wcnf.gz",
"tcp_students_105_it_11.wcnf.gz",
"tcp_students_91_it_9.wcnf.gz",
"tcp_students_91_it_6.wcnf.gz",
"heart_test_3_CNF_4_15.wcnf.gz",
"compas_test_3_DNF_1_10.wcnf.gz",
"heart_test_8_DNF_3_5.wcnf.gz",
"adult_test_6_DNF_2_15.wcnf.gz",
"ionosphere_test_7_DNF_1_5.wcnf.gz",
"ilpd_train_3_CNF_4_15.wcnf.gz",
"ilpd_train_2_CNF_4_10.wcnf.gz",
"310-95.wcnf.gz",
"role_smallcomp_0.75_11.wcnf.gz",
"role_smallcomp_0.25_2.wcnf.gz",
"role_smallcomp_0.85_8.wcnf.gz",
"random-same-4.rna.pre.wcnf.gz",
"random-same-19.rna.pre.wcnf.gz",
"random-same-20.rna.pre.wcnf.gz",
"random-same-5.rna.pre.wcnf.gz",
"random-dif-21.rna.pre.wcnf.gz",
"random-dif-14.rna.pre.wcnf.gz",
"random-dif-3.rna.pre.wcnf.gz",
"openstreetmap.dimacs.wcnf.gz",
"wikipedia.dimacs.wcnf.gz",
"facebook1.dimacs.wcnf.gz",
"guardian.dimacs.wcnf.gz",
"londonist.dimacs.wcnf.gz",
"archlinux.dimacs.wcnf.gz",
"dblp.dimacs.wcnf.gz",
"amazon.dimacs.wcnf.gz",
"ebay.dimacs.wcnf.gz",
"RSN_Security_Min_Witness-Shortest-FlexScan-DB.wcnf.gz",
"RSN_Security_Min_Witness-Shortest-FlexScan-D5.wcnf.gz",
"RSN_Security_Min_Witness-Shortest-MBIST_100cores_20controllers_5memories_na-D5.wcnf.gz",
"RSN_Security_Min_Witness-Shortest-FlexScan-D1.wcnf.gz",
"RSN_Security_Min_Witness-Shortest-MBIST_100cores_20controllers_5memories_na-DC.wcnf.gz",
"RSN_Security_Min_Witness-Shortest-MBIST_100cores_100controllers_5memories_na-DE.wcnf.gz",
"RSN_Security_Min_Witness-Shortest-FlexScan-DC.wcnf.gz",
"RSN_Security_Min_Witness-Shortest-MBIST_100cores_20controllers_5memories_na-DB.wcnf.gz",
"RSN_Security_Min_Witness-Shortest-MBIST_100cores_20controllers_5memories_na-DF.wcnf.gz",
"RSN_Security_Min_Witness-Shortest-MBIST_100cores_20controllers_5memories_na-D4.wcnf.gz",
"random-net-30-6_network-9.net.wcnf.gz",
"random-net-100-1_network-6.net.wcnf.gz",
"random-net-40-5_network-8.net.wcnf.gz",
"random-net-50-2_network-10.net.wcnf.gz",
"random-net-100-1_network-5.net.wcnf.gz",
"random-net-260-1_network-6.net.wcnf.gz",
"random-net-50-5_network-4.net.wcnf.gz",
"random-net-60-2_network-2.net.wcnf.gz",
"random-net-280-1_network-3.net.wcnf.gz",
"random-net-180-1_network-2.net.wcnf.gz",
"random-net-60-1_network-5.net.wcnf.gz",
"random-net-50-3_network-10.net.wcnf.gz",
"instance1.wcnf.gz",
"geffe128_7.wcnf.gz",
"wolfram80_0.wcnf.gz",
"geffe128_3.wcnf.gz",
"wolfram72_6.wcnf.gz",
"wolfram80_7.wcnf.gz",
"geffe128_2.wcnf.gz",
"wolfram80_3.wcnf.gz",
"wolfram72_9.wcnf.gz",
"geffe128_0.wcnf.gz",
"threshold128_1.wcnf.gz",
"wolfram72_3.wcnf.gz",
"wolfram80_5.wcnf.gz",
"driverlog04cc.wcsp.wcnf.gz",
"bwt7.wcsp.wcnf.gz",
"bwt3cc.wcsp.wcnf.gz",
"driverlog02bc.wcsp.wcnf.gz",
"driverlog02cc.wcsp.wcnf.gz",
"logistics01c.wcsp.dir.wcnf.gz",
"mprime03c.wcsp.dir.wcnf.gz",
"driverlog04cc.wcsp.dir.wcnf.gz",
"driverlog01cc.wcsp.dir.wcnf.gz",
"depot01cc.wcsp.dir.wcnf.gz",
"mprime01cc.wcsp.dir.wcnf.gz",
"driverlog02bc.wcsp.dir.wcnf.gz",
"Subnetwork_7_weighted.wcnf.gz",
"Subnetwork_9_weighted.wcnf.gz",
"SingleDay_3_weighted.wcnf.gz",
"brock400_2.clq.wcnf.gz",
"MANN_a45.clq.wcnf.gz",
"johnson8-2-4.clq.wcnf.gz",
"brock200_3.clq.wcnf.gz",
"hamming6-4.clq.wcnf.gz",
"johnson16-2-4.clq.wcnf.gz",
"c-fat200-1.clq.wcnf.gz",
"c-fat200-2.clq.wcnf.gz",
"p_hat300-3.clq.wcnf.gz",
"c-fat500-5.clq.wcnf.gz",
"file_qc_wcnf_N6_H21_2.wcnf.gz",
"file_qc_wcnf_N8_H38_3.wcnf.gz",
"file_qc_wcnf_N8_H38_0.wcnf.gz",
"file_qc_wcnf_N10_H60_1.wcnf.gz",
"file_qc_wcnf_N6_H21_1.wcnf.gz",
"file_qc_wcnf_N10_H60_3.wcnf.gz",
"file_qc_wcnf_N10_H60_4.wcnf.gz",
"file_qc_wcnf_N9_H48_1.wcnf.gz",
"file_qc_wcnf_N8_H38_2.wcnf.gz",
"file_qc_wcnf_N9_H48_3.wcnf.gz",
"file_qc_wcnf_N7_H29_2.wcnf.gz",
"file_qc_wcnf_N6_H21_0.wcnf.gz",
"simNo_7-s_15-m_50-n_50-fp_0.01-fn_0.05.wcnf.gz",
"simNo_10-s_15-m_50-n_50-fp_0.0001-fn_0.20.wcnf.gz",
"408.wcsp.dir.wcnf.gz",
"509.wcsp.dir.wcnf.gz",
"42.wcsp.dir.wcnf.gz",
"54.wcsp.dir.wcnf.gz",
"505.wcsp.dir.wcnf.gz",
"1502.wcsp.log.wcnf.gz",
"404.wcsp.log.wcnf.gz",
"54.wcsp.log.wcnf.gz",
"503.wcsp.log.wcnf.gz",
"414.wcsp.log.wcnf.gz",
"412.wcsp.log.wcnf.gz",
"8.wcsp.log.wcnf.gz",
"MinWidthCB_milan_100_12_1k_5s_2t_7.wcnf.gz",
"MinWidthCB_milan_100_12_1k_2s_1t_2.wcnf.gz",
"MinWidthCB_milan_200_12_1k_2s_2t_4.wcnf.gz",
"Rounded_CorrelationClustering_Protein2_UNARY_N260.wcnf.gz",
"Rounded_CorrelationClustering_Protein4_UNARY_N190.wcnf.gz",
"Rounded_CorrelationClustering_Protein1_UNARY_N190.wcnf.gz",
"Rounded_CorrelationClustering_Protein3_UNARY_N260.wcnf.gz",
"Rounded_CorrelationClustering_Protein2_TRANSITIVE_N200.wcnf.gz",
"f1-DataDisplay_0_order4.seq-B-2-combined-abcdeir.wcnf.gz",
"f49-DC_TotalLoss.seq-B-2-combined-abcdeir.wcnf.gz",
"f49-DC_TotalLoss.seq-B-2-1-abcdeir.wcnf.gz",
"f1-DataDisplay_0_order4.seq-A-2-1-irabcde.wcnf.gz",
"f1-DataDisplay_0_order4.seq-A-3-1-EDCBAir.wcnf.gz",
"f49-DC_TotalLoss.seq-A-2-combined-EDCBAir.wcnf.gz",
"f49-DC_TotalLoss.seq-A-3-combined-irabcde.wcnf.gz",
"f1-DataDisplay_0_order4.seq-A-2-2-abcdeir.wcnf.gz",
"f1-DataDisplay_0_order4.seq-B-2-2-irabcde.wcnf.gz",
"f49-DC_TotalLoss.seq-B-2-2-EDCBAir.wcnf.gz",
"f1-DataDisplay_0_order4.seq-A-2-2-irEDCBA.wcnf.gz",
"f1-DataDisplay_0_order4.seq-B-3-combined-abcdeir.wcnf.gz",
"Rounded_BTWBNSL_asia_100_1_3.scores_TWBound_2.wcnf.gz",
"Rounded_BTWBNSL_asia_1000_1_3.scores_TWBound_3.wcnf.gz",
"CSG60-60-88.wcnf.gz",
"CSG40-40-95.wcnf.gz",
"CSGNaive70-70-91.wcnf.gz",
"CSGNaive60-60-53.wcnf.gz",
"test55--n-7500.wcnf.gz",
"test42--n-7500.wcnf.gz",
"test13--n-2500.wcnf.gz",
"test49--n-7500.wcnf.gz",
"test23--n-5000.wcnf.gz",
"test52--n-7500.wcnf.gz",
"test72--n-10000.wcnf.gz",
"test79--n-10000.wcnf.gz",
"test30--n-5000.wcnf.gz",
"test61--n-10000.wcnf.gz",
"test8--n-2500.wcnf.gz",
"test41--n-7500.wcnf.gz",
"scp49_weighted.wcnf.gz",
"scp46_weighted.wcnf.gz",
"scp47_weighted.wcnf.gz",
"scp51_weighted.wcnf.gz",
"scp65_weighted.wcnf.gz",
"scp64_weighted.wcnf.gz",
"scpnre3_weighted.wcnf.gz",
"scpnrf4_weighted.wcnf.gz",
"scpnrf3_weighted.wcnf.gz",
"scpnre1_weighted.wcnf.gz",
"scpnre4_weighted.wcnf.gz",
"scpnrf2_weighted.wcnf.gz",
"ar-3.wcnf.gz",
"rc-3.wcnf.gz",
"pa-1.wcnf.gz",
"rc-2.wcnf.gz",
"ar-1.wcnf.gz",
"rail582.wcnf.gz",
"rail507.wcnf.gz",
"rail516.wcnf.gz",
]
