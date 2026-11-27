
    #[test]
    fn saturated_memo_preserves_bounded_interleaved_reuse() {
        let mut table = TypeTable::new();
        let arrays: Vec<TypeId> = (0..100)
            .map(|index| {
                let literal = table.number_literal(&index.to_string());
                table.array(literal)
            })
            .collect();
        let number = table.number();
        let numbers = table.array(number);
        let mut target = table.object_type(vec![PropertyType::new("value", false, number)]);
        for _ in 0..12 {
            target = table.object_type(vec![
                PropertyType::new("left", false, target),
                PropertyType::new("middle", false, numbers),
                PropertyType::new("right", false, target),
            ]);
        }
        let mut sources = Vec::new();
        for graph in 0..128 {
            let leaf = table.number_literal(&(1000 + graph * 13).to_string());
            let mut source = table.object_type(vec![PropertyType::new("value", false, leaf)]);
            for level in 0..12 {
                let literal = table.number_literal(&(1001 + graph * 13 + level).to_string());
                let middle = table.array(literal);
                source = table.object_type(vec![
                    PropertyType::new("left", false, source),
                    PropertyType::new("middle", false, middle),
                    PropertyType::new("right", false, source),
                ]);
            }
            sources.push(source);
        }
        let relations = TypeRelations::new(&table);
        for &source in &arrays {
            for &target in &arrays {
                assert_eq!(relations.assignable(source, target), source == target);
            }
        }
        assert_eq!(relations.clean_pairs(), RELATION_CACHE_CAPACITY);
        assert_eq!(relations.cached_pairs(), RELATION_CACHE_CAPACITY);
        let mut work = Vec::new();
        for (graph, source) in sources.into_iter().enumerate() {
            let before = relations.computed_relations();
            let compatible = relations.assignable(source, target);
            let computed = relations.computed_relations() - before;
            eprintln!(
                "MEMO_INTERLEAVED graph={graph} compatible={compatible} computed={computed} clean={} contextual={}",
                relations.clean_pairs(),
                relations.cached_pairs(),
            );
            assert!(compatible);
            assert!(relations.clean_pairs() <= RELATION_CACHE_CAPACITY);
            assert!(relations.cached_pairs() <= RELATION_CACHE_CAPACITY);
            work.push(computed);
        }
        assert_eq!(work.len(), 128);
        assert!(
            work.iter().all(|&computed| computed < 100),
            "bounded interleaving recomputed shared children: {work:?}",
        );
    }
