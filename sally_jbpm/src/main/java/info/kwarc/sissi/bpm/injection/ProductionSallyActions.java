package info.kwarc.sissi.bpm.injection;

import info.kwarc.sally.core.workflow.SallyTask;
import info.kwarc.sally.core.workflow.WorkItemHandler;

import java.util.HashMap;
import java.util.Set;

import org.reflections.Reflections;
import org.reflections.scanners.TypeAnnotationsScanner;
import org.reflections.util.ClasspathHelper;
import org.reflections.util.ConfigurationBuilder;
import org.slf4j.Logger;

import com.google.inject.AbstractModule;
import com.google.inject.TypeLiteral;
import com.google.inject.name.Names;

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
			if (cls == null)
				continue;
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
	}

}
