package info.kwarc.sissi.bpm.injection;

import info.kwarc.sally.core.SallyAction;
import info.kwarc.sally.core.interfaces.SallyTask;
import info.kwarc.sissi.bpm.handlers.DynamicApplyHandler;
import info.kwarc.sissi.bpm.handlers.SallyTaskHandler;

import java.util.Set;

import org.drools.process.instance.WorkItemHandler;
import org.reflections.Reflections;
import org.reflections.scanners.TypeAnnotationsScanner;
import org.reflections.util.ClasspathHelper;
import org.reflections.util.ConfigurationBuilder;
import org.reflections.util.FilterBuilder;
import org.slf4j.Logger;

import com.google.inject.AbstractModule;
import com.google.inject.name.Names;

/**
 * This module makes sure that SallyActions as well as DynamicApplicability are 
 * executed by running the real implementations
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
		.filterInputsBy(new FilterBuilder().includePackage("info.kwarc"))
		.setUrls(ClasspathHelper.forPackage("info.kwarc"))
		.setScanners(new TypeAnnotationsScanner()));

		log = org.slf4j.LoggerFactory.getLogger(this.getClass());

		Set<Class<?>> tasks = reflections.getTypesAnnotatedWith(SallyTask.class);
		for (Class<?> cls : tasks) {
			String action = cls.getAnnotation(SallyTask.class).action();
			if (SallyAction.class.isAssignableFrom(cls)) {
				bind(SallyAction.class).annotatedWith(Names.named(action)).to((Class<? extends SallyAction>)cls);
			} else {
				log.error("Class "+cls+" is annotated with SallyTask but does not implement SallyAction and hence will be ignored.");
			}
		}
		bind(SallyTaskHandler.class);
		bind(DynamicApplyHandler.class);

		bind(WorkItemHandler.class).annotatedWith(Names.named("SallyTask")).to(SallyTaskHandler.class);
		bind(WorkItemHandler.class).annotatedWith(Names.named("DynamicApplicability")).to(DynamicApplyHandler.class);

	}

}
