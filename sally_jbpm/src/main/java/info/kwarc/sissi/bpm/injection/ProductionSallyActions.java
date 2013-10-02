package info.kwarc.sissi.bpm.injection;

import info.kwarc.sally.core.interfaces.SallyTask;
import info.kwarc.sissi.bpm.tasks.DynamicApplyHandler;

import java.util.HashMap;
import java.util.Set;

import org.drools.process.instance.WorkItemHandler;
import org.hibernate.engine.NamedSQLQueryDefinition;
import org.reflections.Reflections;
import org.reflections.scanners.TypeAnnotationsScanner;
import org.reflections.util.ClasspathHelper;
import org.reflections.util.ConfigurationBuilder;
import org.reflections.util.FilterBuilder;
import org.slf4j.Logger;

import com.google.inject.AbstractModule;
import com.google.inject.TypeLiteral;
import com.google.inject.name.Names;
import com.sun.xml.bind.v2.runtime.Name;

/**
 * This module establishes the how boxes in BPMN 
 * @author cjucovschi
 *
 */
public class ProductionSallyActions extends AbstractModule {
	Logger log;

	@Override
	protected void configure() {
		/**
		 * 
		 */
		Reflections reflections = new Reflections(new ConfigurationBuilder()
		.setUrls(ClasspathHelper.forPackage("info.kwarc"))
		.setScanners(new TypeAnnotationsScanner()));

		log = org.slf4j.LoggerFactory.getLogger(this.getClass());

		HashMap<String, Class<? extends WorkItemHandler>> handlers = new HashMap<String, Class<? extends WorkItemHandler>>();
		
		Set<Class<?>> tasks = reflections.getTypesAnnotatedWith(SallyTask.class);
		for (Class<?> cls : tasks) {
			String action = cls.getAnnotation(SallyTask.class).action();
			if (WorkItemHandler.class.isAssignableFrom(cls)) {
				if (handlers.containsKey(action)) {
					log.error("Task Name "+action+" is handled by both "+cls.getCanonicalName()+" and "+handlers.get(action).getCanonicalName());
					continue;
				}
				handlers.put(action, (Class <?extends WorkItemHandler>) cls);
			} else {
				log.error("Class "+cls+" is annotated with SallyTask but does not implement WorkItemHandler and hence will be ignored.");
			}
		}
		
		bind(new TypeLiteral<HashMap<String, Class<? extends WorkItemHandler>>>(){}).annotatedWith(Names.named("WorkItemHandlers")).toInstance(handlers);
		
		bind(DynamicApplyHandler.class);

		bind(WorkItemHandler.class).annotatedWith(Names.named("DynamicApplicability")).to(DynamicApplyHandler.class);

	}

}
