create table tests (
	testId int NOT NULL AUTO_INCREMENT,
	testName text NOT NULL,
	existsInDb BOOLEAN DEFAULT False,
	numQuestions varchar(255) DEFAULT "",
	duration varchar(255) DEFAULT "",
	syllabus text,
	testLink text,
	PRIMARY KEY (testId)
);


create table questions (
	testId int NOT NULL,
	questionId int NOT NULL AUTO_INCREMENT,
	question text NOT NULL,
	answer varchar(255) DEFAULT NULL,
	PRIMARY KEY (questionId),
	FOREIGN KEY (testId) REFERENCES tests(testId)
);


eyashwant@gmail.com