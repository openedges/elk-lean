/*******************************************************************************
 * Copyright (c) 2026 elk-lean contributors.
 *
 * Adapted from elk-rs scripts/java/ElkModelParityExportTest.java (EPL-2.0).
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * http://www.eclipse.org/legal/epl-2.0.
 *
 * SPDX-License-Identifier: EPL-2.0 OR GPL-3.0-or-later
 *******************************************************************************/
package org.eclipse.elk.lean.baseline;

import java.io.BufferedWriter;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Locale;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.eclipse.elk.alg.disco.options.DisCoMetaDataProvider;
import org.eclipse.elk.alg.force.options.ForceMetaDataProvider;
import org.eclipse.elk.alg.force.options.StressMetaDataProvider;
import org.eclipse.elk.alg.layered.options.LayeredMetaDataProvider;
import org.eclipse.elk.alg.mrtree.options.MrTreeMetaDataProvider;
import org.eclipse.elk.alg.radial.options.RadialMetaDataProvider;
import org.eclipse.elk.alg.rectpacking.options.RectPackingMetaDataProvider;
import org.eclipse.elk.alg.spore.options.SporeMetaDataProvider;
import org.eclipse.elk.alg.topdownpacking.options.TopdownpackingMetaDataProvider;
import org.eclipse.elk.alg.vertiflex.options.VertiFlexMetaDataProvider;
import org.eclipse.elk.core.RecursiveGraphLayoutEngine;
import org.eclipse.elk.core.data.LayoutMetaDataService;
import org.eclipse.elk.core.options.CoreOptions;
import org.eclipse.elk.core.util.BasicProgressMonitor;
import org.eclipse.elk.core.util.Maybe;
import org.eclipse.elk.core.util.persistence.ElkGraphResourceFactory;
import org.eclipse.elk.graph.ElkGraphPackage;
import org.eclipse.elk.graph.ElkNode;
import org.eclipse.elk.graph.json.ElkGraphJson;
import org.eclipse.elk.graph.json.JsonImporter;
import org.eclipse.elk.graph.text.ElkGraphStandaloneSetup;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

/**
 * ELK Java 0.12.0 reference layouts for elk-lean (the result baseline).
 *
 * <p>Initialisation follows ELK's own plain-Java test setup ({@code PlainJavaInitialization}:
 * core options and the providers of disco, force, stress, layered, mrtree, radial, rectpacking,
 * spore, vertiflex; ELK Graph Text for {@code .elkt}, the ELK graph resource factory for
 * {@code .elkg}) plus topdownpacking, which elk-lean also provides. The export contract is the one
 * of elk-rs' Java exporter: JSON models are laid out as they are; {@code .elkt}/{@code .elkg}
 * models are loaded through EMF, get {@code RANDOM_SEED} and are exported to JSON first (all
 * options, positions and sizes), and that JSON is what both ELK Java and elk-lean lay out.
 *
 * <p>With {@code --trace}, the root algorithm is forced to layered (like elk-rs' trace runner and
 * {@code elk batch --trace-dir}) and the layered LGraph after every processor is written to
 * {@code <out_dir>/trace/<model>/step_NNN_<Processor>.json} ({@link ElkPhaseTraceExporter}).
 *
 * <p>Usage: {@code ElkJavaBaseline <models_dir> <out_dir> [--include a,b] [--exclude a,b]
 * [--limit N] [--seed S] [--force-algorithm ID] [--trace true] [--reverse true] [--shuffle SEED]}. {@code --reverse} / {@code --shuffle}
 * processes the models in reverse order: ELK iterates some {@code HashMap}/{@code HashSet}s of
 * objects without their own {@code hashCode} (self-loop port sides, partition members, ...), so its
 * result for such a model depends on the identity hash codes handed out before — i.e. on the run.
 */
public final class ElkJavaBaseline {

    private static final String HEADER = "model_rel_path\tinput_json\tjava_layout_json\tjava_status\tjava_error";

    private ElkJavaBaseline() {
    }

    static void initialize() {
        LayoutMetaDataService.getInstance().registerLayoutMetaDataProviders(
                new CoreOptions(),
                new DisCoMetaDataProvider(),
                new ForceMetaDataProvider(),
                new LayeredMetaDataProvider(),
                new MrTreeMetaDataProvider(),
                new RadialMetaDataProvider(),
                new RectPackingMetaDataProvider(),
                new SporeMetaDataProvider(),
                new StressMetaDataProvider(),
                new VertiFlexMetaDataProvider(),
                new TopdownpackingMetaDataProvider());
        ElkGraphStandaloneSetup.doSetup();
        Resource.Factory.Registry.INSTANCE.getExtensionToFactoryMap().put("elkg", new ElkGraphResourceFactory());
        ElkGraphPackage.eINSTANCE.eClass();
    }

    public static void main(final String[] args) throws IOException {
        if (args.length < 2) {
            System.err.println("usage: ElkJavaBaseline <models_dir> <out_dir> [--include a,b] [--exclude a,b]"
                    + " [--limit N] [--seed S] [--force-algorithm ID]");
            System.exit(2);
        }
        final Path modelsRoot = Paths.get(args[0]).toAbsolutePath().normalize();
        final Path outputDir = Paths.get(args[1]).toAbsolutePath().normalize();
        List<String> include = Collections.emptyList();
        List<String> exclude = Collections.emptyList();
        int limit = 0;
        int seed = 1;
        String forceAlgorithm = null;
        boolean trace = false;
        boolean reverse = false;
        Long shuffleSeed = null;
        for (int i = 2; i + 1 < args.length; i += 2) {
            switch (args[i]) {
            case "--include":
                include = csv(args[i + 1]);
                break;
            case "--exclude":
                exclude = csv(args[i + 1]);
                break;
            case "--limit":
                limit = Integer.parseInt(args[i + 1]);
                break;
            case "--seed":
                seed = Integer.parseInt(args[i + 1]);
                break;
            case "--force-algorithm":
                forceAlgorithm = args[i + 1];
                break;
            case "--trace":
                trace = Boolean.parseBoolean(args[i + 1]);
                break;
            case "--reverse":
                reverse = Boolean.parseBoolean(args[i + 1]);
                break;
            case "--shuffle":
                shuffleSeed = Long.parseLong(args[i + 1]);
                break;
            default:
                throw new IllegalArgumentException("unknown argument " + args[i]);
            }
        }
        initialize();
        final Path inputDir = outputDir.resolve("inputs");
        final Path layoutDir = outputDir.resolve("layouts");
        Files.createDirectories(inputDir);
        Files.createDirectories(layoutDir);
        final List<Path> models = new ArrayList<>(collect(modelsRoot, include, exclude, limit));
        if (reverse) {
            // a second run in a different JVM context: identity hash codes (HashMap/HashSet order of
            // objects without their own hashCode) differ, which exposes ELK's context-dependent results
            Collections.reverse(models);
        }
        if (shuffleSeed != null) {
            Collections.shuffle(models, new java.util.Random(shuffleSeed));
        }
        int ok = 0;
        int failed = 0;
        try (BufferedWriter manifest = Files.newBufferedWriter(outputDir.resolve("java_manifest.tsv"),
                StandardCharsets.UTF_8)) {
            manifest.write(HEADER);
            manifest.newLine();
            for (Path model : models) {
                final String rel = unix(modelsRoot.relativize(model));
                final Path inputJson = inputDir.resolve(rel + ".json");
                final Path layoutJson = layoutDir.resolve(rel + ".json");
                String status = "ok";
                String error = "";
                try {
                    Files.createDirectories(inputJson.getParent());
                    Files.createDirectories(layoutJson.getParent());
                    final boolean isJson = model.getFileName().toString().toLowerCase(Locale.ROOT).endsWith(".json");
                    String input;
                    if (isJson) {
                        input = Files.readString(model, StandardCharsets.UTF_8);
                    } else {
                        ElkNode loaded = load(model);
                        loaded.setProperty(CoreOptions.RANDOM_SEED, seed);
                        input = ElkGraphJson.forGraph(loaded)
                                .prettyPrint(false)
                                .shortLayoutOptionKeys(false)
                                .omitZeroPositions(false)
                                .omitZeroDimension(false)
                                .omitLayout(false)
                                .omitUnknownLayoutOptions(false)
                                .toJson();
                    }
                    Files.writeString(inputJson, input, StandardCharsets.UTF_8);
                    JsonObject json = JsonParser.parseString(input).getAsJsonObject();
                    Maybe<JsonImporter> importer = new Maybe<>();
                    ElkNode graph = ElkGraphJson.forGraph(json).rememberImporter(importer).lenient(false).toElk();
                    if (!isJson) {
                        graph.setProperty(CoreOptions.RANDOM_SEED, seed);
                    }
                    if (forceAlgorithm != null) {
                        graph.setProperty(CoreOptions.ALGORITHM, forceAlgorithm);
                    }
                    if (trace) {
                        graph.setProperty(CoreOptions.ALGORITHM, "org.eclipse.elk.layered");
                        Path traceDir = outputDir.resolve("trace").resolve(rel);
                        Files.createDirectories(traceDir);
                        ElkPhaseTraceExporter.traceWithRecursiveEngine(graph, traceDir, false);
                    } else {
                        new RecursiveGraphLayoutEngine().layout(graph, new BasicProgressMonitor());
                    }
                    importer.get().transferLayout(graph);
                    Files.writeString(layoutJson, json.toString(), StandardCharsets.UTF_8);
                    ok++;
                } catch (Throwable t) {
                    status = "error";
                    error = t.toString().replace('\t', ' ').replace('\n', ' ').replace('\r', ' ');
                    failed++;
                }
                manifest.write(rel + "\t" + inputJson + "\t" + layoutJson + "\t" + status + "\t" + error);
                manifest.newLine();
                manifest.flush();
            }
        }
        System.out.printf(Locale.ROOT, "ELK Java baseline: total=%d ok=%d failed=%d out=%s%n",
                models.size(), ok, failed, outputDir);
    }

    private static ElkNode load(final Path model) throws IOException {
        ResourceSet set = new ResourceSetImpl();
        Resource resource = set.getResource(URI.createFileURI(model.toString()), true);
        if (resource == null) {
            throw new IOException("no EMF resource for " + model);
        }
        resource.load(Collections.emptyMap());
        if (resource.getContents().isEmpty()) {
            throw new IOException("empty model " + model);
        }
        EObject root = resource.getContents().get(0);
        if (!(root instanceof ElkNode)) {
            throw new IOException("model root is not an ElkNode: " + model);
        }
        return (ElkNode) root;
    }

    private static List<Path> collect(final Path root, final List<String> include, final List<String> exclude,
            final int limit) throws IOException {
        try (Stream<Path> stream = Files.walk(root)) {
            List<Path> files = stream.filter(Files::isRegularFile)
                    .filter(p -> {
                        String n = p.getFileName().toString().toLowerCase(Locale.ROOT);
                        return n.endsWith(".json") || n.endsWith(".elkt") || n.endsWith(".elkg");
                    })
                    .filter(p -> matches(root, p, include, true) && !matches(root, p, exclude, false))
                    .sorted(Comparator.comparing(p -> unix(root.relativize(p))))
                    .collect(Collectors.toList());
            return limit > 0 && files.size() > limit ? new ArrayList<>(files.subList(0, limit)) : files;
        }
    }

    private static boolean matches(final Path root, final Path p, final List<String> tokens, final boolean emptyMeans) {
        if (tokens.isEmpty()) {
            return emptyMeans;
        }
        String rel = unix(root.relativize(p)).toLowerCase(Locale.ROOT);
        return tokens.stream().anyMatch(t -> rel.contains(t.toLowerCase(Locale.ROOT)));
    }

    private static List<String> csv(final String raw) {
        return Stream.of(raw.split(",")).map(String::trim).filter(s -> !s.isEmpty()).collect(Collectors.toList());
    }

    private static String unix(final Path p) {
        return p.toString().replace('\\', '/');
    }
}
